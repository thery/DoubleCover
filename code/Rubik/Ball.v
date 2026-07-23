(* ========================================================================= *)
(*  Ball.v                                                                    *)
(*                                                                           *)
(*  The word metric of a generating set in a finite group.                    *)
(*                                                                           *)
(*  `ball S n` is the set of elements that are products of at most n           *)
(*  generators from S -- the closed ball of radius n around the identity in    *)
(*  the Cayley graph of <S>.  These objects are for *reasoning*, not           *)
(*  computation.                                                              *)
(*                                                                           *)
(*  The two facts the Rubik diameter reduction rests on:                      *)
(*   - mem_ballJ : membership is invariant under conjugation by any symmetry   *)
(*     that stabilises the generating set (S :^ u = S).  [the 48 symmetries]   *)
(*   - mem_ballV : membership is invariant under inversion when S is           *)
(*     symmetric (S^-1 = S).                        [the factor-of-2]          *)
(*  Both are proved by rewriting/induction, never by evaluating a permutation. *)
(* ========================================================================= *)

From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Ball.
Variable gT : finGroupType.
Implicit Types (S A B : {set gT}) (u g : gT).

Fixpoint ball S n : {set gT} :=
  if n is n'.+1 then ball S n' :|: ball S n' * S else 1.

Lemma ball0 S : ball S 0 = 1. Proof. by []. Qed.

Lemma mem1_ball S n : 1 \in ball S n.
Proof. by elim: n => [|n IH]; rewrite /= ?(set1gE, inE) ?IH. Qed.

Lemma ball_mono S n : ball S n \subset ball S n.+1.
Proof. by rewrite /= subsetUl. Qed.

(* ---- Conjugation invariance (the spatial symmetries) --------------------- *)

(* Conjugation acts on the balls: (S:^u)^{<=n} = (S^{<=n}):^u. *)
Lemma ballJ S u n : ball (S :^ u) n = (ball S n) :^ u.
Proof. by elim: n => [|n IH]; rewrite /= ?conjs1g // IH conjUg conjsMg. Qed.

(* If u stabilises S, ball-membership is conjugation-invariant.  This is the  *)
(* metric symmetry that collapses the cosets in the diameter reduction.       *)
Lemma mem_ballJ S u g n : S :^ u = S -> (g ^ u \in ball S n) = (g \in ball S n).
Proof.
move=> SJ; have HB : ball S n = (ball S n) :^ u by rewrite -{1}SJ ballJ.
by rewrite {1}HB mem_conjg conjgK.
Qed.

(* ---- Inversion invariance (the factor-of-2) ------------------------------ *)

(* Right multiplication and inversion each distribute over an indexed union. *)
Lemma mulg_bigcup I r (P : pred I) (F : I -> {set gT}) S :
  (\bigcup_(i <- r | P i) F i) * S = \bigcup_(i <- r | P i) (F i * S).
Proof.
by apply: (big_morph (fun A => A * S)) => [A B|]; [exact: mulUg | exact: mul0g].
Qed.

Lemma inv_set0 : (set0 : {set gT})^-1 = set0.
Proof. by apply/setP => x; rewrite mem_invg !inE. Qed.

Lemma invg_bigcup I r (P : pred I) (F : I -> {set gT}) :
  (\bigcup_(i <- r | P i) F i)^-1 = \bigcup_(i <- r | P i) (F i)^-1.
Proof.
by apply: (big_morph (fun A => A^-1)) => [A B|]; [exact: invUg | exact: inv_set0].
Qed.

(* (S^k)^-1 = (S^-1)^k as sets. *)
Lemma invg_expg S k : (S ^+ k)^-1 = (S^-1) ^+ k.
Proof.
elim: k => [|k IH]; first by rewrite !expg0 invg1.
by rewrite expgSr invMg IH -expgS.
Qed.

(* ball as a union of powers -- the presentation that is manifestly closed    *)
(* under inversion (left- and right-built balls coincide).                    *)
Lemma ballE S n : ball S n = \bigcup_(k < n.+1) S ^+ k.
Proof.
elim: n => [|n IH]; first by rewrite big_ord_recl big_ord0 expg0 setU0.
rewrite /= IH mulg_bigcup; apply/setP => x; rewrite inE.
apply/idP/bigcupP => [/orP[]/bigcupP[k _ xk]|[k _ xk]].
- by exists (widen_ord (leqnSn _) k).
- by exists (lift ord0 k) => //; rewrite /= expgSr.
- have [kn|kn] := ltnP k n.+1;
    first by apply/orP; left; apply/bigcupP; exists (Ordinal kn).
  apply/orP; right; apply/bigcupP; exists (Ordinal (ltnSn n)) => //=.
  have kE : (k : nat) = n.+1 by apply/eqP; rewrite eqn_leq kn -ltnS ltn_ord.
  by move: xk; rewrite kE expgSr.
Qed.

Lemma ball_inv S n : (ball S n)^-1 = ball (S^-1) n.
Proof. by rewrite !ballE invg_bigcup; apply: eq_bigr => k _; rewrite invg_expg. Qed.

(* If S is symmetric, ball-membership is inversion-invariant. *)
Lemma mem_ballV S g n : S^-1 = S -> (g^-1 \in ball S n) = (g \in ball S n).
Proof. by move=> SV; rewrite -mem_invg ball_inv SV. Qed.

(* ---- Reachability: ball vs the generated group --------------------------- *)

(* A product of n elements of S is a word of length n, hence lies in S ^+ n.  *)
Lemma mem_prodg_expg S n (c : 'I_n -> gT) :
  (forall i, c i \in S) -> \prod_(i < n) c i \in S ^+ n.
Proof.
elim: n c => [|n IH] c cS; first by rewrite big_ord0 expg0 set1gE inE.
rewrite big_ord_recr expgSr.
by apply: mem_mulg; [apply: IH => i; apply: cS | apply: cS].
Qed.

(* Every element of <<S>> is reached by some finite ball (S generates). *)
Lemma mem_gen_ball S g : g \in <<S>> -> exists n, g \in ball S n.
Proof.
move=> /gen_prodgP[n [c cS ->]].
exists n; rewrite ballE; apply/bigcupP.
by exists (Ordinal (ltnSn n)) => //; apply: mem_prodg_expg.
Qed.

(* Conversely every ball lies inside the generated group. *)
Lemma ball_sub_gen S n : ball S n \subset <<S>>.
Proof.
elim: n => [|n IH]; first by rewrite /= sub1G.
rewrite /= subUset IH /=.
apply: subset_trans (mulgSS IH (sub_gen (subxx S))) _; rewrite mulGid.
exact: subxx.
Qed.

(* ---- The diameter bound and its reduction to coset representatives -------- *)

(* "The Cayley-diameter of <S> is at most n": every element is a word of       *)
(* length <= n.  A covering predicate -- no minimal-length function, no giant  *)
(* nat is ever built.                                                          *)
Definition diam_le S n := <<S>> \subset ball S n.

(* Conjugation by a symmetry that stabilises S preserves the ball-covering    *)
(* test on a set (the set-level lift of mem_ballJ). *)
Lemma sub_ballJ S u C n :
  S :^ u = S -> (C :^ u \subset ball S n) = (C \subset ball S n).
Proof.
move=> SJ; have HB : ball S n = (ball S n) :^ u by rewrite -{1}SJ ballJ.
by rewrite {1}HB conjSg.
Qed.

(* Inversion (when S is symmetric) likewise preserves the covering test. *)
Lemma sub_ballV (S C : {set gT}) n :
  S^-1 = S -> (C^-1 \subset ball S n) = (C \subset ball S n).
Proof.
move=> SV; have HB : ball S n = (ball S n)^-1 by rewrite ball_inv SV.
by rewrite {1}HB invSg.
Qed.

(* If every right coset of a subgroup H <= <<S>> is within radius n, so is    *)
(* the whole group (the cosets partition it).                                 *)
Lemma diam_le_cover S (H : {group gT}) n :
  H \subset <<S>> ->
  (forall C, C \in rcosets H <<S>> -> C \subset ball S n) ->
  diam_le S n.
Proof.
move=> HS cov; rewrite /diam_le -(cover_partition (rcosets_partition HS)).
rewrite /cover; apply/bigcupsP => C CH; exact: cov.
Qed.

(* THE REDUCTION (conjugation only).  It suffices to check a set R of          *)
(* representatives such that every coset is carried into R by some symmetry    *)
(* stabilising S.  [The 48 spatial symmetries.]                               *)
Lemma diam_le_reps S (H : {group gT}) (R : {set {set gT}}) n :
  H \subset <<S>> ->
  (forall C, C \in rcosets H <<S>> ->
     exists2 u, S :^ u = S & C :^ u \in R) ->
  (forall C, C \in R -> C \subset ball S n) ->
  diam_le S n.
Proof.
move=> HS Hrep Hrad; apply: (diam_le_cover HS) => C CH.
have [u SJ CuR] := Hrep C CH.
by rewrite -(sub_ballJ C n SJ); apply: Hrad.
Qed.

(* THE REDUCTION (conjugation + inversion).  Each coset reaches a checked      *)
(* representative by a symmetry stabilising S, possibly composed with          *)
(* inversion.  [The 48 symmetries x the factor of 2 = 96.]  R need not consist *)
(* of cosets: it is just the set of representatives one has verified.          *)
Lemma diam_le_reps2 S (H : {group gT}) (R : {set {set gT}}) n :
  H \subset <<S>> -> S^-1 = S ->
  (forall C, C \in rcosets H <<S>> ->
     exists2 u, S :^ u = S & (C :^ u \in R) || (C^-1 :^ u \in R)) ->
  (forall D, D \in R -> D \subset ball S n) ->
  diam_le S n.
Proof.
move=> HS SV Hrep Hrad; apply: (diam_le_cover HS) => C CH.
have [u SJ] := Hrep C CH.
case/orP=> DR.
  by rewrite -(sub_ballJ C n SJ); exact: (Hrad _ DR).
by rewrite -(sub_ballV C n SV) -(sub_ballJ (C^-1) n SJ); exact: (Hrad _ DR).
Qed.

(* ---- Symmetry of a generating set --------------------------------------- *)

(* A set closed under taking inverses is its own image under inversion.  Used  *)
(* to show the Rubik move set is symmetric (S^-1 = S), the hypothesis of the   *)
(* inversion half of the diameter reduction.                                   *)
Lemma invg_closed_setV (S : {set gT}) :
  {in S, forall x, x^-1 \in S} -> S^-1 = S.
Proof.
move=> Sinv; apply/setP => x; rewrite mem_invg.
apply/idP/idP => xS; last exact: Sinv.
by rewrite -(invgK x); apply: Sinv.
Qed.

(* A half turn is an involution: if g has order dividing 4 then g^+2 is its    *)
(* own inverse.  This is what makes the half turns g^+2 stay in the move set    *)
(* under inversion. *)
Lemma half_turn_inv g : g ^+ 4 = 1 -> (g ^+ 2) ^-1 = g ^+ 2.
Proof. by move=> g4; apply: (mulgI (g ^+ 2)); rewrite mulgV -expgnDr g4. Qed.

End Ball.
