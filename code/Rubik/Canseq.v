(* How many sequences of moves the rules leave.                              *)
(*                                                                           *)
(* Rokicki, Kociemba, Davidson and Dethridge count these with an 18 x 18     *)
(* matrix, collapsed to 6 x 6, and derive                                    *)
(*                                                                           *)
(*     q(n) = 12 q(n-1) + 18 q(n-2).                                         *)
(*                                                                           *)
(* It collapses further, to two numbers.  The amount of a turn is free --    *)
(* the rules only look at faces -- so q(n) = 3^n p(n) where p counts FACE    *)
(* sequences.  And the six faces fall into two classes: after one of U, R, F *)
(* the opposite face is cut by the order convention, and after one of D, L,  *)
(* B it is not.  Writing a(n) and b(n) for the face sequences ending in each *)
(* class,                                                                    *)
(*                                                                           *)
(*     a(n+1) = 2 a(n) + 3 b(n)        a low face has 2 low and 2 high heirs *)
(*     b(n+1) = 2 a(n) + 2 b(n)        a high face has 3 low and 2 high      *)
(*                                                                           *)
(* and the recurrence above is two lines of arithmetic on that pair.         *)

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

(* the paper's recurrence *)
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

(* THE ONE STEP LEFT.  Peeling the first face off a canonical sequence is a   *)
(* bijection onto the pairs (g, shorter sequence) with g allowed after f.     *)
(* Everything below it is arithmetic; this is the only combinatorial content, *)
(* and it is where the tuple plumbing lives.                                  *)
Lemma cntS n f : cnt n.+1 f = \sum_(g | allowed f g) cnt n g.
Proof. Admitted.

(* With it, the two classes are the two numbers, and the count is p.          *)
(* cnt does not depend on the face itself, only on whether it is low.         *)
Lemma cnt_class n (f g : 'I_6) :
  ((f : nat) < 3) = ((g : nat) < 3) -> cnt n f = cnt n g.
Proof. Admitted.

Theorem canseq_pc n : canseq n = pc n.
Proof. Admitted.

Theorem canseq_rec n : canseq n.+2 = 4 * canseq n.+1 + 2 * canseq n.
Proof. by rewrite !canseq_pc pc_rec. Qed.
