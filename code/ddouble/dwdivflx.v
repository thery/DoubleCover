From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error Mult_error BinarySingleNaN PrimFloat.
From Flocq Require Import Pff.Pff2Flocq.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum dwprod dwflx.
From dwarith Require Import DWDivDW.

(* The quotient of two double words, read in the format with no bottom.       *)
(*                                                                            *)
(* `dw_updn.v' bounds `divDwDw2' by a shift of sixteen units in the last      *)
(* place, and sixteen is the paper's own constant: `DWDivDW.v' holds          *)
(* Theorem 7.1, admit-free, for `DWDivDW2', which is `divDwDw2' step for      *)
(* step, and it reads `15 u^2 + 56 u^3'.  What stands between that theorem    *)
(* and the program is this file: the theorem is over the reals in the format  *)
(* with no smallest exponent, the program runs primitive floats in the        *)
(* bounded one.  `dwflx.v' is the same road built for the SUM; this is the    *)
(* quotient's.                                                                *)
(*                                                                            *)
(* THE QUOTIENT IS HARDER THAN THE SUM, and for one reason.  A sum of two     *)
(* floats too small for the bounded format to round is exact, so neither      *)
(* format rounds it and they agree with nothing asked - that is               *)
(* `Drnd_FLX_plus' of dwflx.v.  A product and a quotient have no such         *)
(* property: below the smallest normal number the bounded format rounds and   *)
(* the other does not.  Hence every lemma here that touches one carries a     *)
(* range condition, and hence the quotient's BOUND needs a range test where   *)
(* the sum's needs none.                                                      *)

Open Scope R_scope.

(* A product and a quotient, where the two formats agree.                     *)
Lemma Drnd_FLX_mult a b :
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  Drnd (D2R a * D2R b) = Xrnd (D2R a * D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

Lemma Drnd_FLX_div a b :
  (Dnorm <= Rabs (D2R a / D2R b))%R ->
  Drnd (D2R a / D2R b) = Xrnd (D2R a / D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

(* The high word of the two-product is the rounded product, and the two       *)
(* formats agree on it once it is normal.                                     *)
Lemma twoProd_hi_FLX a b :
  Dfin a -> Dfin b -> Dfin (a * b)%float ->
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) = Xrnd (D2R a * D2R b).
Proof.
move=> Fa Fb Fp Hn.
have [Ep _] := Dfin_mul _ _ Fa Fb Fp.
by rewrite /twoProd /dekker /=; case: (splitC a) => ??; case: (splitC b) => ??;
   rewrite /= Ep; apply: Drnd_FLX.
Qed.

(* The smallest product the two-product does not miss: two to the minus nine  *)
(* hundred and sixty-nine.  Flocq's own theorem gives exactness above it and  *)
(* only the three-and-a-half smallest numbers below, and dwprod.v takes the   *)
(* second half of that; this is the first half.                               *)
Notation Dprodlo := (bpow radix2 (SpecFloat.emin prec emax + 2 * prec - 1)).

Theorem twoProd_exact a b : Dfin (dwlo (twoProd a b)) ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) + D2R (dwlo (twoProd a b)) = D2R a * D2R b.
Proof.
rewrite dekkerE /= => Fe Hn.
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
have [H _] := Dekker radix2 (SpecFloat.emin prec emax) prec
   (fun n => negb (Z.even n)) Hp4 Hemin (D2R a) (D2R b) Fa2 Fb2 Hbeta.
rewrite -DfexpE -!DrndE in H.
by rewrite -H //; right.
Qed.

(* And so the two-product computes, in the format with no bottom, exactly     *)
(* the pair the paper's `Fast2Mult' does: the rounded product, and the error  *)
(* of it, which that format holds exactly.  This is the fact the paper        *)
(* assumes of its own two-product, and the note beside that assumption reads  *)
(* "or Dekker's algorithm" - Dekker's algorithm is what this is.              *)
Lemma twoProd_FLX a b :
  Dfin a -> Dfin b -> Dfin (a * b)%float -> Dfin (dwlo (twoProd a b)) ->
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) = Xrnd (D2R a * D2R b) /\
  D2R (dwlo (twoProd a b)) =
    Xrnd (D2R a * D2R b - Xrnd (D2R a * D2R b)).
Proof.
move=> Fa Fb Fp Fe Hn Hp.
have Ehi := twoProd_hi_FLX _ _ Fa Fb Fp Hn.
have Hex := twoProd_exact _ _ Fe Hp.
split => //.
have Hlo : D2R (dwlo (twoProd a b)) =
           (D2R a * D2R b - Xrnd (D2R a * D2R b))%R by rewrite -Ehi; lra.
rewrite Hlo.
(* The error of a product is itself a number of this format, so the rounding *)
(* of it is itself.  `round_generic' has to be aimed at the OUTER rounding:   *)
(* left to find its own target it takes the inner one and asks for the        *)
(* product to be a number of the format, which it is not.                     *)
have Hp0 : Prec_gt_0 prec by [].
have Hf : Xformat (D2R a * D2R b - Xrnd (D2R a * D2R b)).
  rewrite -Ropp_minus_distr; apply: generic_format_opp.
  by apply: mult_error_FLX; exact: Dformat_FLX.
by rewrite (round_generic _ _ _ _ Hf).
Qed.
