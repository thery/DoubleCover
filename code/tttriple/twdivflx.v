From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From Flocq Require Import Pff.Pff2Flocq.
From mathcomp Require Import all_ssreflect.
From twarith.threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From twarith.threewords Require Import TwoSum TWR VecSum VSEB.
From twarith.threewords Require Import ThreeProd ThreeProdDW ThreeProdOne.
From twarith.threewords Require Import ThreeReci ThreeDiv ThreeSqRt.
From twarith Require Import twarith twbound twpaper twseed twdivn twflx.
From dwarith Require Import dwbridge dwtwosum dwprod dwbound dwflx dwsqrt.

(* THE QUOTIENT ACROSS THE BRIDGE.                                            *)
(*                                                                            *)
(* Algorithm 14 is the reciprocal's seed and three products, and the three    *)
(* products crossed with the root: `threeProdDW_XT' and `threeProdOneTW_XT'   *)
(* are in `twflx.v'.  What is left is the seed and the `2 - _'.               *)

Notation XreciA := (reciA prec Dchoice).
Notation XreciH11 := (reciH11 prec Dchoice).
Notation XreciH1n := (reciH1n prec Dchoice).
Notation XreciB01 := (reciB01 prec Dchoice).
Notation XreciB11 := (reciB11 prec Dchoice).
Notation XreciB12n := (reciB12n prec Dchoice).
Notation XreciBWn := (reciBWn prec Dchoice).
Notation XThreeDivN := (ThreeDivN prec Dchoice).

Open Scope R_scope.

(* The two literals the seed is tilted by.                                    *)
Lemma Donep : D2R onep = (1 + 2 * u prec radix2)%R.
Proof. by rewrite /D2R /onep (u_pow prec); compute; lra. Qed.

Lemma Donem : D2R onem = (1 - 2 * u prec radix2)%R.
Proof. by rewrite /D2R /onem (u_pow prec); compute; lra. Qed.

Lemma Dfin_onep : Dfin onep.
Proof. by rewrite /Dfin /onep; compute. Qed.

Lemma Dfin_onem : Dfin onem.
Proof. by rewrite /Dfin /onem; compute. Qed.

(* WHAT THE SEED ASKS.  The `h11' line is where the machine and the paper     *)
(* part company in shape and meet in value: the paper writes one fused        *)
(* `RN(a x0 - (1 + 2u))' and the machine takes the two-product's low word     *)
(* round the houses, `(p - (1 + 2u)) + e'.  They agree because `p' IS         *)
(* `1 + 2u' -- that is what tilting `a' by it was for -- so the subtraction   *)
(* is nought and what is left is `e', which is the fused line's value.        *)
Definition reciBW_ok (x0 x1 : PrimFloat.float) : Prop :=
  let a := (onep / x0)%float in
  let pe := twoProd a x0 in
  let h11 := ((dwhi pe - onep) + dwlo pe)%float in
  let h1 := (- h11 - a * x1)%float in
  let b01 := dwhi (twoProd a onem) in
  let b11 := dwlo (twoProd a onem) in
  let b12 := (b11 + a * h1)%float in
  [/\ Dfin x0, Dfin x1, (D2R x0 <> 0)%R & Dfin a]
  /\ (Dnorm <= Rabs (D2R onep / D2R x0))%R
  /\ [/\ Dfin (dwlo pe), Dfin (dwhi pe - onep)%float, Dfin h11,
         Dfin b11 & Dfin b12]
  /\ [/\ mulOkR (D2R a) (D2R x0), mulOkR (D2R a) (D2R onem),
         mulOkR (D2R a) (D2R x1) & mulOkR (D2R a) (D2R h1)]
  /\ [/\ Dfin (a * x1)%float, Dfin h1 & Dfin (a * h1)%float]
  /\ DfastTwoSumFin b01 b12.

Lemma reciBW_X x0 x1 :
  reciBW_ok x0 x1 ->
  tw2R (reciBW x0 x1) = XreciBWn (D2R x0) (D2R x1).
Proof.
rewrite /reciBW_ok
  => [] [[Fx0 Fx1 Nx0 Fa] [Hdiv [[Fe Fpm Fh11 Fb11 Fb12]
        [[M0 M1 M2 M3] [[Max1 Fh1 Mah1] Hfast]]]]].
have Hp2 : (1 < prec)%Z by [].
have Hp10 : (10 <= prec)%Z by [].
(* the reciprocal *)
have Ea : D2R (onep / x0)%float = XreciA (D2R x0).
  by rewrite (div_X _ _ Dfin_onep Nx0 Fa Hdiv) Donep.
set a := (onep / x0)%float in Fa Hdiv M0 M1 M2 M3 Max1 Mah1 Ea *.
(* the `h11' line, which the two make the same number of                     *)
have [Ep Ee] := twoProd_XO _ _ Fe M0.
rewrite Ea in Ep Ee.
have Hr : Xrnd (D2R x0 * XreciA (D2R x0)) = (1 + 2 * u prec radix2)%R
  by apply: (round_div_1p2u Hp2 Hp10 (choice := Dchoice) Dchoice_sym) => //;
     apply: Dformat_FLX.
have Ep1 : D2R (dwhi (twoProd a x0)) = (1 + 2 * u prec radix2)%R.
  by rewrite Ep /MULTmore.TwoProd /= (Rmult_comm (XreciA (D2R x0))) Hr.
have Fdp : Dfin (dwhi (twoProd a x0)).
  by have [_ [_ []]] := twoProd_hi _ _ Fe.
have Epm : D2R (dwhi (twoProd a x0) - onep)%float = 0%R.
  rewrite (sub_X _ _ Fdp Dfin_onep Fpm) Ep1 Donep.
  have -> : (1 + 2 * u prec radix2 - (1 + 2 * u prec radix2) = 0)%R by ring.
  by apply: round_0.
have Eh11 : D2R ((dwhi (twoProd a x0) - onep) + dwlo (twoProd a x0))%float
          = XreciH11 (D2R x0).
  rewrite (add_X _ _ Fpm Fe Fh11) Epm Rplus_0_l round_generic;
    last by apply: Dformat_FLX.
  rewrite Ee /MULTmore.TwoProd /= (Rmult_comm (XreciA (D2R x0))) Hr.
  by rewrite (Rmult_comm (D2R x0)).
set h11 := ((dwhi (twoProd a x0) - onep) + dwlo (twoProd a x0))%float
  in Fh11 Fh1 Eh11 *.
(* the first split line *)
have Eh1 : D2R (- h11 - a * x1)%float = XreciH1n (D2R x0) (D2R x1).
  rewrite (sub_X _ _ (Dfin_opp _ Fh11) Max1 Fh1) D2R_opp Eh11.
  by rewrite (mul_XO _ _ Fa Fx1 Max1 M2) Ea.
set h1 := (- h11 - a * x1)%float in Fh1 Mah1 M3 Eh1 *.
(* the two-product against `1 - 2u', and the last split line *)
have [Eb01 Eb11] := twoProd_XO _ _ Fb11 M1.
rewrite Ea Donem in Eb01 Eb11.
set b01 := dwhi (twoProd a onem) in Hfast Eb01 *.
set b11 := dwlo (twoProd a onem) in Fb11 Hfast Eb11 *.
have Eb12 : D2R (b11 + a * h1)%float = XreciB12n (D2R x0) (D2R x1).
  rewrite (add_X _ _ Fb11 Mah1 Fb12) (mul_XO _ _ Fa Fh1 Mah1 M3) Ea Eb11 Eh1.
  by rewrite /reciB12n.
set b12 := (b11 + a * h1)%float in Fb12 Hfast Eb12 *.
have Fb01 : Dfin b01 by have [_ [_ []]] := twoProd_hi _ _ Fb11.
have [Ebh Ebl] := fastTwoSum_X _ _ Fb01 Fb12 Hfast.
rewrite Eb01 Eb12 in Ebh Ebl.
rewrite /reciBW -/a.
rewrite (dwE (twoProd a x0)) -/h11 -/h1.
rewrite (dwE (twoProd a onem)) -/b01 -/b11 -/b12.
rewrite (dwE (fastTwoSum b01 b12)).
rewrite /XreciBWn /reciBWn /reciBn /tw2R /=.
have E0 : D2R 0%float = 0%R by rewrite /D2R; compute; lra.
by rewrite Ebh Ebl E0.
Qed.

(* Two less a triple word: exact on the leading word, and the two-sum says    *)
(* so, exactly as for three halves less one.                                  *)
Definition sub2Tw_ok (t : twfloat) : Prop :=
  let: TWFloat x0 x1 x2 := t in
  [/\ Dfin x0, Dfin x1, Dfin x2, Dfin (2 - x0)%float
    & (D2R (2 - x0)%float = 2 - D2R x0)%R].

Lemma sub2Tw_X t : sub2Tw_ok t -> tw2R (sub2Tw t) = sub2TW (tw2R t).
Proof.
case: t => x0 x1 x2 [F0 F1 F2 Fs He].
by rewrite /sub2Tw /sub2TW /tw2R /= He !D2R_opp.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Algorithm 14                                                              *)
(* ---------------------------------------------------------------------------*)

Definition div_ok (z x : twfloat) : Prop :=
  let bw := reciBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  let s2 := sub2Tw i1 in
  let az := threeProdDW bw z in
  reciBW_ok (tw0 x) (tw1 x)
  /\ prodDW_ok (tw0 bw) (tw1 bw) (tw0 x) (tw1 x) (tw2 x)
  /\ prodDW_ok (tw0 bw) (tw1 bw) (tw0 z) (tw1 z) (tw2 z)
  /\ sub2Tw_ok i1
  /\ prodOne_ok (tw0 az) (tw1 az) (tw2 az) (tw1 s2) (tw2 s2).

Lemma threeDiv_X z x : div_ok z x ->
  tw2R (threeDiv z x) = XThreeDivN (tw2R z) (tw2R x).
Proof.
rewrite /div_ok /threeDiv /ThreeDivN /ThreeDivAuxN
  => [] [Hseed [Hp1 [Hp2 [Hsub Hp3]]]].
have Ebw : tw2R (reciBW (tw0 x) (tw1 x))
         = XreciBWn (D2R (tw0 x)) (D2R (tw1 x)) by apply: reciBW_X.
rewrite (threeProdOneTW_XT _ _ Hp3) (sub2Tw_X _ Hsub)
        (threeProdDW_XT _ _ Hp1) (threeProdDW_XT _ _ Hp2) Ebw.
by case: x {Hseed Hp1 Hp2 Hsub Hp3 Ebw}.
Qed.
