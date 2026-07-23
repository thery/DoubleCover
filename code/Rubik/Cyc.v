(* ========================================================================= *)
(*  Cyc.v                                                                     *)
(*                                                                           *)
(*  Cyclic permutations of a finite type, presented by a list of the points  *)
(*  they cycle.  `cyc [:: a0; a1; ...; ak]` is the permutation                *)
(*     a0 -> a1 -> ... -> ak -> a0,  fixing everything else.                  *)
(*  It is built as a product of transpositions, so it carries no injectivity  *)
(*  proof obligation.  The three lemmas characterise it fully on a `uniq`     *)
(*  list -- purely by rewriting, never by evaluating a permutation.           *)
(* ========================================================================= *)

From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma in_rcons (T : eqType) y s (x : T) :
  (x \in rcons s y) = (x == y) || (x \in s).
Proof. by elim: s => //= z s IH;  rewrite !inE IH orbCA. Qed.

Section Cyc.

Variable A : finType.

Definition cyc (s : seq A) : {perm A} :=
  if s is a0 :: rest then \prod_(a <- rest) tperm a0 a else 1%g.

Lemma cyc_notin a l : a \notin l -> cyc l a = a.
Proof.
case: l => [|b] /=; first by rewrite permE.
elim => [|c l IH aL]; rewrite !(big_cons, big_nil, mulg1, permE) //=.
rewrite tpermD ?IH //; move: aL; rewrite !inE !negb_or.
- by case/and3P => ->.
- by case/and3P => ? _ _; rewrite eq_sym.
by case/and3P => _ ? _; rewrite eq_sym.
Qed.

Lemma cyc_succ a b l1 l2 :
  uniq (l1 ++ a :: b :: l2) -> cyc (l1 ++ a :: b :: l2) a = b.
Proof.
case: l1 => [|c l1].
  rewrite cat0s /cyc !(big_cons, big_nil, mulg1, permE) /= tpermL.
  rewrite !inE !negb_or => /and3P[/andP[? ?] ? ?].
  by rewrite [LHS](@cyc_notin b (a :: l2)) // !inE !negb_or; apply/andP;
     split; rewrite 1?eq_sym.
elim: l1 => [|d l1 IH] /=.
  rewrite !inE !negb_or => /and3P[/and3P[? ? ?] /andP[? ?] /andP[? ?]].
  rewrite !(big_cons, big_nil, mulg1, permE) /= tpermR permE /= tpermL //.
  rewrite [LHS](@cyc_notin b (c :: l2)) //.
  by rewrite inE negb_or; apply/andP; rewrite 1?eq_sym.
rewrite !inE !negb_or => /and3P[/andP[H1 H2] H3 H4].
rewrite big_cons !permE /= tpermD ?IH //=.
- by apply/andP; split.
- by rewrite mem_cat negb_or inE negb_or in H2; case/and3P: H2.
by rewrite mem_cat negb_or inE negb_or in H3; case/and3P: H3.
Qed.

Lemma cyc_head a b l :
  uniq (a :: rcons l b) -> cyc (a :: rcons l b) b = a.
Proof.
rewrite /=.
elim: l => [|c l IH] /=; rewrite !(big_cons, big_nil, mulg1, permE) /=.
  by rewrite tpermR permE.
rewrite !inE !in_rcons !negb_or => /and3P[/andP[? /andP[? ?]] /andP[? ?] ?].
rewrite permE /= ifN; last by rewrite eq_sym.
rewrite ifN ?IH ?in_rcons ?negb_or //; last by rewrite eq_sym.
by rewrite -andbA; apply/and3P; split.
Qed.

End Cyc.
