From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From Flocq Require Import Pff.Pff2Flocq.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dwtwosum.

(* The two-product of dwarith.v, read on the reals.                           *)
(* Splitting a number in two and multiplying the halves is Dekker's way of    *)
(* getting the error of a product without a fused multiply-add.  Flocq has    *)
(* that theorem already, in the bounded format, and the program here is it    *)
(* step for step: the same splitting constant, the same five additions.       *)
(* So all this file does is say which real number each float operation        *)
(* computes, and hand the result over.                                        *)
(*                                                                            *)
(* Unlike the two-sum, the two-product is not always error free: below two    *)
(* to the minus nine hundred and sixty-nine the two words can miss the        *)
(* product, though never by more than three and a half times the smallest     *)
(* number there is.  That is the bound proved here, and it holds              *)
(* everywhere, so no case has to be split.                                    *)

Open Scope R_scope.

(* The splitting constant is two to the twenty-seven, plus one, which is      *)
(* what the theorem asks for at this precision.                               *)
Lemma Dc_const : D2R c_const = bpow radix2 (prec - Z.div2 prec) + 1.
Proof. by rewrite /D2R /c_const; compute; lra. Qed.

Notation Dsplc := (bpow radix2 (prec - Z.div2 prec) + 1).
Notation Dhalf a := (Drnd (Drnd (D2R a - Drnd (D2R a * Dsplc))
                           + Drnd (D2R a * Dsplc))).

(* One splitting, read on the reals.  Every step is a rounded real            *)
(* operation as soon as none of the four overflows, and the last of them      *)
(* being a number is enough to know that of all four.                         *)
Lemma splitCE a : Dfin (dwlo (splitC a)) ->
  Dfin a /\ Dfin (dwhi (splitC a)) /\
  D2R (dwhi (splitC a)) = Dhalf a /\
  D2R (dwlo (splitC a)) = Drnd (D2R a - Dhalf a).
Proof.
move=> Ft.
have [Fa Fh] := Dfin_subI _ _ Ft.
have [Fp Fq] := Dfin_addI _ _ Fh.
have [_ Fpa] := Dfin_subI _ _ Fq.
have Fc : Dfin c_const by [].
have [Ep _] := Dfin_mul _ _ Fc Fa Fp.
have Epa : D2R (c_const * a)%float = Drnd (D2R a * Dsplc).
  by rewrite Ep Dc_const Rmult_comm.
have [Eq _] := Dfin_sub _ _ Fa Fp Fq.
have Eqa : D2R (a - c_const * a)%float = Drnd (D2R a - Drnd (D2R a * Dsplc)).
  by rewrite Eq Epa.
have [Eh _] := Dfin_add _ _ Fp Fq Fh.
have Eha : D2R (dwhi (splitC a)) = Dhalf a.
  by rewrite /= Eh Epa Eqa (Rplus_comm (Drnd (D2R a * Dsplc))).
have [Et _] := Dfin_sub _ _ Fa Fh Ft.
by split => //; split => //; split => //=; rewrite Et Eha.
Qed.

(* The product, with its two halves named rather than hidden in a match.      *)
Lemma dekkerE a b :
  twoProd a b =
  DWFloat (a * b)
    ((((- (a * b) + dwhi (splitC a) * dwhi (splitC b))
       + dwhi (splitC a) * dwlo (splitC b))
       + dwlo (splitC a) * dwhi (splitC b))
       + dwlo (splitC a) * dwlo (splitC b))%float.
Proof.
by rewrite /twoProd /dekker; case: (splitC a) => ha ta; case: (splitC b).
Qed.

(* How far the two words can be from the product.  One test carries the       *)
(* whole computation, as with the two-sum: each of the seventeen numbers      *)
(* is an argument of the operation that made the next, so the last one        *)
(* being a number proves they all were.                                       *)
Theorem twoProd_err a b : Dfin (dwlo (twoProd a b)) ->
  Rabs (D2R a * D2R b -
        (D2R (dwhi (twoProd a b)) + D2R (dwlo (twoProd a b))))
  <= 7 / 2 * bpow radix2 (SpecFloat.emin prec emax).
Proof.
rewrite dekkerE /= => Fe.
have [Ft3 Ftatb] := Dfin_addI _ _ Fe.
have [Fta Ftb] := Dfin_mulI _ _ Ftatb.
have [Ft2 Ftahb] := Dfin_addI _ _ Ft3.
have [_ Fhb] := Dfin_mulI _ _ Ftahb.
have [Ft1 Fhatb] := Dfin_addI _ _ Ft2.
have [Fha _] := Dfin_mulI _ _ Fhatb.
have [Fnpi Fhahb] := Dfin_addI _ _ Ft1.
have Fpi := Dfin_oppI _ Fnpi.
have [Fa Fb] := Dfin_mulI _ _ Fpi.
have [_ [_ [Eha Eta]]] := splitCE _ Fta.
have [_ [_ [Ehb Etb]]] := splitCE _ Ftb.
rewrite (proj1 (Dfin_add _ _ Ft3 Ftatb Fe)).
rewrite (proj1 (Dfin_add _ _ Ft2 Ftahb Ft3)).
rewrite (proj1 (Dfin_add _ _ Ft1 Fhatb Ft2)).
rewrite (proj1 (Dfin_add _ _ Fnpi Fhahb Ft1)).
rewrite (proj1 (Dfin_mul _ _ Fta Ftb Ftatb)).
rewrite (proj1 (Dfin_mul _ _ Fta Fhb Ftahb)).
rewrite (proj1 (Dfin_mul _ _ Fha Ftb Fhatb)).
rewrite (proj1 (Dfin_mul _ _ Fha Fhb Fhahb)).
rewrite D2R_opp (proj1 (Dfin_mul _ _ Fa Fb Fpi)).
rewrite Eha Eta Ehb Etb.
have Hp0 : Prec_gt_0 prec by [].
have Hp4 : (4 <= prec)%Z by [].
have Hemin : (SpecFloat.emin prec emax < 0)%Z by [].
have Fa2 : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R a) by rewrite -DfexpE; apply: Dformat.
have Fb2 : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R b) by rewrite -DfexpE; apply: Dformat.
have Hbeta : (radix_val radix2 = 2%Z) \/ Z.Even prec by left.
have [_ H] := Dekker radix2 (SpecFloat.emin prec emax) prec
   (fun n => negb (Z.even n)) Hp4 Hemin (D2R a) (D2R b) Fa2 Fb2 Hbeta.
by rewrite -DfexpE -!DrndE in H.
Qed.
