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

End Ball.
