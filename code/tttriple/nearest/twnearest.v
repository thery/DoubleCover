From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Reals Psatz.
From dwarith Require Import dwbridge dwbound.
From twarith Require Import twarith twbound.
Require Import PrimInt63 Floats.

(* THE ROUND-TO-NEAREST TRIPLE WORD, AND THE SORT THE PRODUCT USED TO DO.     *)
(*                                                                            *)
(* Nothing on the build path calls any of this.  It is kept because it is     *)
(* what an obvious implementation looks like, and the distance between it and *)
(* what `tw_ops.v' runs is the argument for the paper's algorithms -- see     *)
(* `nearest/README.md'.  Build it by hand:                                    *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../../ddouble dwarith \         *)
(*        nearest/twnearest.v                                                 *)

Open Scope R_scope.

Definition dw2tw d := TWFloat (dwhi d) (dwlo d) 0.

(* Putting a list in order of decreasing size.  Both sweeps below ask for     *)
(* their terms in that order: what they do is push what one term cannot       *)
(* hold down to the next, and a term out of place is one the sweep walks      *)
(* past.  Sorting moves the terms about and so changes nothing at all about   *)
(* what the list stands for.                                                  *)
Fixpoint insMag (x : float) (l : seq float) : seq float :=
  match l with
  | [::] => [:: x]
  | a :: l' => if (abs a <=? abs x)%float then x :: l else a :: insMag x l'
  end.

Definition sortMag (l : seq float) : seq float := foldr insMag [::] l.


Arguments sortMag : simpl never.

(* ===========================================================================*)
(*  The operations, rounded to nearest                                        *)
(* ===========================================================================*)

(* The sum of two triple words: merge the six terms, sweep, and keep the      *)
(* first three.  What is dropped is the whole of the error.                    *)
Definition plusTwTw (x y : twfloat) :=
  l2tw (take 3 (vseb (vecSum (Merge (tw2l x) (tw2l y))))).

Definition subTwTw x y := plusTwTw x (negTw y).

(* The product of two triple words.  The four products that carry the value   *)
(* come back as two words each; the five that are smaller than the last word  *)
(* of the answer are taken as they are.  Which of the thirteen numbers is     *)
(* the largest depends on the two triple words, so they are put in order      *)
(* before the sweeps, which is what the sweeps ask for.  Nothing in that      *)
(* changes what the list stands for, and the first three terms are kept.      *)
Definition timesTwTw (x y : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat y0 y1 y2 := y in
  let: DWFloat p00 e00 := twoProd x0 y0 in
  let: DWFloat p01 e01 := twoProd x0 y1 in
  let: DWFloat p10 e10 := twoProd x1 y0 in
  let: DWFloat p11 e11 := twoProd x1 y1 in
  l2tw (take 3 (vseb (vecSum (sortMag
    [:: p00; p01; p10; p11; e00; e01; e10; e11;
        (x0 * y2)%float; (x2 * y0)%float;
        (x1 * y2)%float; (x2 * y1)%float; (x2 * y2)%float])))).

Definition timesTwFp x f := timesTwTw x (fp2tw f).

(* The quotient of two triple words, by long division: divide the leading     *)
(* word of what is left by the leading word of the divisor, take that much    *)
(* out, and repeat.  Three rounds give the three words.  The rounds after     *)
(* the first work on a remainder, so nothing about the first one has to be    *)
(* good.                                                                      *)
Definition divTwTw (x y : twfloat) :=
  let y0 := tw0 y in
  let t1 := (tw0 x / y0)%float in
  let r1 := subTwTw x (timesTwFp y t1) in
  let t2 := (tw0 r1 / y0)%float in
  let r2 := subTwTw r1 (timesTwFp y t2) in
  let t3 := (tw0 r2 / y0)%float in
  toTw t1 t2 t3.

(* The square root, by Newton's method: the average of a guess and the        *)
(* number divided by it.  The machine root of the three words added is the    *)
(* guess, good to sixteen digits; one step takes it to thirty-two and a       *)
(* second to sixty-four, which is past the forty-eight a triple word holds.   *)
Definition sqrtTw (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let s := fp2tw (PrimFloat.sqrt (x0 + x1 + x2)%float) in
  let s1 := halfTw (plusTwTw s (divTwTw x s)) in
  halfTw (plusTwTw s1 (divTwTw x s1)).


(* And so does putting one in order of size.                                  *)
Lemma insMag_sum x l : sumL (insMag x l) = D2R x + sumL l.
Proof.
by elim: l => [|a l IH] /=; [lra | case: (abs a <=? abs x)%float; rewrite /= ?IH; lra].
Qed.

Lemma sortMag_sum l : sumL (sortMag l) = sumL l.
Proof. by elim: l => [|x l IH] //=; rewrite /sortMag /= insMag_sum IH. Qed.


(* Reading a sorted or swept list back to the one it came from: each is a     *)
(* rearrangement or a sweep, so the answer being made of numbers proves the   *)
(* list was.                                                                  *)
Lemma insMag_finI x l : finL (insMag x l) -> Dfin x /\ finL l.
Proof.
elim: l => [|a l IH] /=; first by case=> Fx _.
case: (abs a <=? abs x)%float => /=; first by case=> Fx [Fa Fl].
by case=> Fa /IH [Fx Fl].
Qed.

Lemma sortMag_finI l : finL (sortMag l) -> finL l.
Proof.
elim: l => [|x l IH] //=.
by rewrite /sortMag /= => /insMag_finI [Fx /IH Fl].
Qed.


(* ===========================================================================*)
(*  What they compute                                                         *)
(* ===========================================================================*)

Compute plusTwTw (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute timesTwTw (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute divTwTw (fp2tw 1) (fp2tw 3).
Compute timesTwTw (divTwTw (fp2tw 1) (fp2tw 3)) (fp2tw 3).
Compute sqrtTw (fp2tw 2).
Compute timesTwTw (sqrtTw (fp2tw 2)) (sqrtTw (fp2tw 2)).
