(* How many sequences of moves the rules leave.                               *)
(*                                                                            *)
(* Rokicki, Kociemba, Davidson and Dethridge count these with an 18 x 18      *)
(* matrix, collapsed to 6 x 6, and derive                                     *)
(*                                                                            *)
(*     q(n) = 12 q(n-1) + 18 q(n-2).                                          *)
(*                                                                            *)
(* It collapses further, to two numbers.  The amount of a turn is free --     *)
(* the rules only look at faces -- so q(n) = 3^n p(n) where p counts FACE     *)
(* sequences.  And the six faces fall into two classes: after one of U, R, F  *)
(* the opposite face is cut by the order convention, and after one of D, L,   *)
(* B it is not.  Writing a(n) for the face sequences that start with one of   *)
(* D, L, B and b(n) for those that start with one of U, R, F,                 *)
(*                                                                            *)
(*     a(n+1) = 2 a(n) + 3 b(n)      one of D, L, B is followed by 2 of its   *)
(*     b(n+1) = 2 a(n) + 2 b(n)      own kind and 3 of the other, one of      *)
(*                                   U, R, F by 2 and 2                       *)
(*                                                                            *)
(* and the recurrence above is two lines of arithmetic on that pair.          *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the rule ------------------------------------------------------------ *)

(* Faces in the order U R F D L B, so opposites are three apart and the order *)
(* convention is just "less than".  Then "g is the opposite of f and comes    *)
(* after it" says exactly g = f + 3, which is why no modular arithmetic is    *)
(* needed here at all.                                                        *)
Definition allowed (f g : 'I_6) := (g != f) && ((g : nat) != f + 3).

(* ---- the two numbers ----------------------------------------------------- *)

Fixpoint ab (n : nat) : nat * nat :=
  if n is m.+1 then let: (a, b) := ab m in (2 * a + 3 * b, 2 * a + 2 * b)
  else (3, 3).

(* p n counts the face sequences of length n+1, q n the move sequences.       *)
Definition pc n := (ab n).1 + (ab n).2.
Definition qc n := 3 ^ n.+1 * pc n.

Lemma abS n :
  ab n.+1 = (2 * (ab n).1 + 3 * (ab n).2, 2 * (ab n).1 + 2 * (ab n).2).
Proof. by rewrite /=; case: (ab n). Qed.

Lemma pc_rec n : pc n.+2 = 4 * pc n.+1 + 2 * pc n.
Proof. by rewrite /pc !abS /= -!plusE -!multE; lia. Qed.

(* the paper's recurrence                                                     *)
Lemma qc_rec n : qc n.+2 = 12 * qc n.+1 + 18 * qc n.
Proof. by rewrite /qc pc_rec !expnS -!plusE -!multE; lia. Qed.

(* Table 5.1 of the paper, for as far as unary arithmetic will go:            *)
(*   pc = 6, 27, 120, 534, 2376  and  3^4 * 534 = 43254, 3^5 * 2376 = 577368  *)

(* ---- what those numbers count -------------------------------------------- *)

(* A face sequence is canonical when consecutive faces are allowed; `path' is *)
(* exactly that predicate.  cnt n f counts the canonical sequences of n more  *)
(* faces after an initial f.                                                  *)
Definition cnt n (f : 'I_6) := #|[set s : n.-tuple 'I_6 | path allowed f s]|.

Definition canseq n := \sum_(f : 'I_6) cnt n f.

(* Peeling the first face off a canonical sequence is a bijection onto the    *)
(* pairs (g, shorter sequence) with g allowed after f.  This is the only      *)
(* combinatorial step; everything below it is arithmetic.                     *)
Lemma cntS n f : cnt n.+1 f = \sum_(g | allowed f g) cnt n g.
Proof.
rewrite /cnt -!sum1_card.
rewrite [RHS](eq_bigr (fun g => \sum_(s : n.-tuple 'I_6 | path allowed g s) 1));
    last first.
  by move=> g _; rewrite -sum1_card; apply: eq_bigl => s; rewrite inE.
rewrite (eq_bigl (fun s : n.+1.-tuple 'I_6 => path allowed f s)); last first.
  by move=> s; rewrite inE.
rewrite pair_big_dep.
have hbij : bijective (fun p : 'I_6 * n.-tuple 'I_6 => [tuple of p.1 :: p.2]).
  exists (fun s : n.+1.-tuple 'I_6 => (thead s, [tuple of behead s])).
    move=> [g s]; apply/eqP; rewrite xpair_eqE /=.
    by apply/andP; split; apply/eqP; last apply: val_inj.
  by move=> s; rewrite -tuple_eta.
rewrite (reindex _ (onW_bij _ hbij)).
by apply: eq_bigl => -[g s].
Qed.

(* Length zero leaves the empty sequence and nothing else.                    *)
Lemma cnt0 (f : 'I_6) : cnt 0 f = 1.
Proof.
by rewrite /cnt -[RHS](card_tuple 0 'I_6); apply: eq_card => s; rewrite inE;
   case: s => -[|a l].
Qed.

(* The two numbers are the two counts, each taken over the three faces of     *)
(* its class -- which is where the factor three comes from.  Both facts       *)
(* below are read off this one.                                               *)
Lemma cntE n (f : 'I_6) :
  3 * cnt n f = (if (f : nat) < 3 then (ab n).2 else (ab n).1).
Proof.
elim: n f => [f|n IH f]; first by rewrite cnt0 muln1; case: leqP.
rewrite cntS big_distrr /=.
under eq_bigr => g _ do rewrite IH.
case: (ab n) => a b /=.
case: f => -[|[|[|[|[|[|//]]]]]] Hf;
  rewrite big_mkcond !big_ord_recl big_ord0 /allowed /=;
  by rewrite -!plusE -!multE; lia.
Qed.

(* cnt does not depend on the face itself, only on whether it is low.         *)
Lemma cnt_class n (f g : 'I_6) :
  ((f : nat) < 3) = ((g : nat) < 3) -> cnt n f = cnt n g.
Proof.
by move=> Hfg; apply/eqP; rewrite -(eqn_pmul2l (isT : 0 < 3)) !cntE Hfg.
Qed.

(* Six faces, three of each class, so the total is a + b.                     *)
Theorem canseq_pc n : canseq n = pc n.
Proof.
apply/eqP; rewrite -(eqn_pmul2l (isT : 0 < 3)) /canseq big_distrr /=.
under eq_bigr => f _ do rewrite cntE.
rewrite !big_ord_recl big_ord0 /pc /=.
by apply/eqP; rewrite -!plusE -!multE; lia.
Qed.

Theorem canseq_rec n : canseq n.+2 = 4 * canseq n.+1 + 2 * canseq n.
Proof. by rewrite !canseq_pc pc_rec. Qed.
