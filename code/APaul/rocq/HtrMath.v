(** * T6: the mathematics of the search of htr3.c, no Capla

    Two facts the proof of the Capla htr3 needs (doc/htr3-capla-plan.typ):
    (a) the table the search builds from the values of a polynomial gives
    the polynomial at [j] in its first coefficient, plus the window, modulo
    [beta^l]; (b) the test of [hscan] implies the top-word test of htr3.c.
    The search walks [j = 0 .. n-1], as [TaylorLink.hscan_exp] does. *)

From Stdlib Require Import ZArith Reals Lia List.
From APaulRocq Require Import HtrDefs TaylorReal.
From mathcomp Require Import all_ssreflect all_algebra ssrZ zify.
From APaulRocq Require Import Shift TaylorScan TaylorLink.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** (a) From the values [P(0) .. P(k-1)] modulo [beta^l], [k] the number
    of coefficients of [P], the table after [j] steps holds
    [P(j) + err beta^(l-1)] in its first coefficient, modulo [beta^l]. *)
Lemma table_head (A : list Z) (L err : Z) (j : nat) :
  Z.le 1 L ->
  Z.modulo (List.nth 0 (table L err
              (List.map (fun i => Z.modulo (polyZ A (Z.of_nat i)) (baseZ L))
                        (List.seq 0 (List.length A))) j) Z0) (baseZ L) =
  Z.modulo (Z.add (polyZ A (Z.of_nat j))
                  (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1)))))
           (baseZ L).
Proof.
Admitted.

(** (b) The test of [hscan], [(b + E) mod beta^l <= 2 E] with
    [E = err beta^(l-1)], implies the top-word test of htr3.c. *)
Lemma top_hit (L err b : Z) :
  Z.le 1 L -> Z.le 0 err ->
  Z.le (Z.modulo (Z.add b (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1)))))
                 (baseZ L))
       (Z.mul 2 (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1))))) ->
  Z.le (top L (Z.add b (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1))))))
       (Z.mul 2 err).
Proof.
Admitted.
