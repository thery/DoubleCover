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
(*  The key fact for the Rubik diameter reduction is `mem_ballJ`: the metric   *)
(*  is invariant under any symmetry `u` that stabilises the generating set     *)
(*  (`S :^ u = S`).  Applied once per spatial symmetry of the cube, this is    *)
(*  what makes cosets in the same symmetry class equidistant, collapsing the   *)
(*  2.2*10^9 cosets to the ~5.6*10^7 the paper actually searches.              *)
(* ========================================================================= *)

From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Ball.
Variable gT : finGroupType.
Implicit Types (S A : {set gT}) (u g : gT).

Fixpoint ball S n : {set gT} :=
  if n is n'.+1 then ball S n' :|: ball S n' * S else 1.

Lemma ball0 S : ball S 0 = 1. Proof. by []. Qed.

Lemma mem1_ball S n : 1 \in ball S n.
Proof. by elim: n => [|n IH]; rewrite /= ?(set1gE, inE) ?IH. Qed.

Lemma ball_mono S n : ball S n \subset ball S n.+1.
Proof. by rewrite /= subsetUl. Qed.

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

End Ball.
