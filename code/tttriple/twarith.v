From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.

(* THE PAIR AND THE ERROR-FREE TRANSFORMS ARE `code/ddouble''s, NOT A COPY.   *)
(* `twoSum', `fastTwoSum', the splitting and Dekker's product are the same    *)
(* lines either way, and they say nothing about pairs beyond returning one.   *)
(* Declaring them again here would declare a second `dwfloat' with them, and  *)
(* then nothing proved of the first would apply -- and what is proved of the  *)
(* first is what the sweeps below need most: `twoSum' is exact               *)
(* (`dwtwosum.v'), and the two-product misses by at most three and a half of  *)
(* the smallest number there is (`dwprod.v').                                 *)
From dwarith Require Export dwarith.

(* Triple words on primitive floats: the algorithms, with nothing proved.     *)
(*                                                                            *)
(* A triple word is three binary64 floats standing for their sum.  Three      *)
(* words hold about forty-eight decimal digits where one holds sixteen and    *)
(* two hold thirty-two.                                                       *)
(*                                                                            *)
(* The algorithms are those of the three-word paper, whose proofs are in      *)
(* `threewords/`, with one difference forced by the machine: Rocq's           *)
(* primitive floats have no fused multiply-add.  Every step the paper writes  *)
(* as one rounding of `a + b * c` is written here as two, and the             *)
(* error-free product is Dekker's splitting rather than the one-instruction   *)
(* one.  So a value computed here is not the paper's to the last bit; what    *)
(* is asked of it is only a bound, and a bound survives the change.           *)

(* A triple of floats: the format itself.                                     *)
Inductive twfloat := TWFloat (x0 : float) (x1 : float) (x2 : float).

Implicit Type d : dwfloat.
Implicit Type t : twfloat.
Implicit Type f : float.

Definition tw0 t := let: TWFloat x0 _ _ := t in x0.
Definition tw1 t := let: TWFloat _ x1 _ := t in x1.
Definition tw2 t := let: TWFloat _ _ x2 := t in x2.

(* Each word is small enough beside the one before it that adding it back     *)
(* changes nothing.  This is the separation the paper asks of a triple        *)
(* word, in the one form a program can test.                                 *)
Definition wellFormed t :=
  let: TWFloat x0 x1 x2 := t in
  ((x0 + x1 =? x0) && (x1 + x2 =? x1))%float.

Definition fp2tw f := TWFloat f 0 0.
Definition dw2tw d := TWFloat (dwhi d) (dwlo d) 0.
(* ===========================================================================*)
(*  Expansions: a list of floats standing for its sum                         *)
(* ===========================================================================*)

(* Two words need no machinery of their own; three do.  A list of floats      *)
(* standing for its sum is the paper's way, and the two passes below turn     *)
(* any such list into a separated one without changing what it stands for.    *)

(* One sweep of two-sums from the end of the list to the front.  The sum is   *)
(* unchanged, and the largest term comes out in front.                        *)
Fixpoint vecSumAux (l : seq float) : seq float * float :=
  match l with
  | [::]    => ([::], 0%float)
  | [:: x]  => ([::], x)
  | x :: l' => let: (es, s) := vecSumAux l' in
               let d := twoSum x s in
               (dwlo d :: es, dwhi d)
  end.

Definition vecSum (l : seq float) : seq float :=
  let: (es, s0) := vecSumAux l in s0 :: es.

(* The second sweep, front to back, which drops the terms that came out       *)
(* nought and separates what is left.  The sum is unchanged again.            *)
Fixpoint vsebAux (eps : float) (l : seq float) : seq float :=
  match l with
  | [::]       => [:: eps]
  | [:: elast] => let d := twoSum eps elast in [:: dwhi d; dwlo d]
  | e :: l'    => let d := twoSum eps e in
                  if (dwlo d =? 0)%float then vsebAux (dwhi d) l'
                  else dwhi d :: vsebAux (dwlo d) l'
  end.

Definition vseb (l : seq float) : seq float :=
  if l is e0 :: l' then vsebAux e0 l' else [::].

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

(* Merging two lists already in order of size keeps them in order of size.    *)
Fixpoint Merge (l1 : seq float) : seq float -> seq float :=
  fix Merge_aux (l2 : seq float) : seq float :=
    match l1, l2 with
    | [::], _ => l2
    | _, [::] => l1
    | a1 :: l1', a2 :: l2' =>
        if (abs a2 <=? abs a1)%float
        then a1 :: Merge l1' l2
        else a2 :: Merge_aux l2'
    end.

Definition tw2l t := let: TWFloat x0 x1 x2 := t in [:: x0; x1; x2].

(* A list read back as a triple word, short lists filled out with noughts.    *)
Definition l2tw (l : seq float) :=
  match l with
  | [:: r0, r1, r2 & _] => TWFloat r0 r1 r2
  | [:: r0; r1]         => TWFloat r0 r1 0
  | [:: r0]             => TWFloat r0 0 0
  | [::]                => TWFloat 0 0 0
  end.

(* Three floats as a triple word: both sweeps, and nothing lost.              *)
Definition toTw (a b c : float) := l2tw (vseb (vecSum [:: a; b; c])).

(* ===========================================================================*)
(*  The operations, rounded to nearest                                        *)
(* ===========================================================================*)

(* The sum of two triple words: merge the six terms, sweep, and keep the      *)
(* first three.  What is dropped is the whole of the error.                    *)
Definition plusTwTw (x y : twfloat) :=
  l2tw (take 3 (vseb (vecSum (Merge (tw2l x) (tw2l y))))).

Definition negTw t :=
  let: TWFloat x0 x1 x2 := t in TWFloat (- x0) (- x1) (- x2).

Definition subTwTw x y := plusTwTw x (negTw y).

(* Halving a triple word: every word moves by one exponent, and no rounding   *)
(* loses anything except at the very bottom of the range.                      *)
Definition halfTw t :=
  let: TWFloat x0 x1 x2 := t in
  TWFloat (x0 / 2)%float (x1 / 2)%float (x2 / 2)%float.

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

(* ===========================================================================*)
(*  What the algorithms compute                                               *)
(* ===========================================================================*)

Compute toTw 1 1e-20 1e-40.
Compute plusTwTw (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute timesTwTw (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute divTwTw (fp2tw 1) (fp2tw 3).
Compute timesTwTw (divTwTw (fp2tw 1) (fp2tw 3)) (fp2tw 3).
Compute sqrtTw (fp2tw 2).
Compute timesTwTw (sqrtTw (fp2tw 2)) (sqrtTw (fp2tw 2)).
