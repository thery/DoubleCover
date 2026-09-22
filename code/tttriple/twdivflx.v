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

(* ---------------------------------------------------------------------------*)
(*  The guard, as a test                                                      *)
(* ---------------------------------------------------------------------------*)

(* ALGORITHM 13'S TEST, THE WAY `code/ddouble' WRITES ONE: a range test on   *)
(* each of the four products, read where the seed left them, and ONE         *)
(* finiteness test.  Everything else follows: the last word is a sum of the  *)
(* one before it, which is a product of the one before that, all the way     *)
(* back to the two-products, and `twoProd_finI' carries those.               *)
Definition reciBW_okb (x0 x1 : PrimFloat.float) : bool :=
  let a := (onep / x0)%float in
  let pe := twoProd a x0 in
  let ax0 := dwhi pe in
  let pm := (ax0 - onep)%float in
  let h11 := (pm + dwlo pe)%float in
  let ax1 := (a * x1)%float in
  let h1 := (- h11 - ax1)%float in
  let bp := twoProd a onem in
  let b01 := dwhi bp in
  let b11 := dwlo bp in
  let ah1 := (a * h1)%float in
  let b12 := (b11 + ah1)%float in
  [&& (0 <? abs x0)%float, normF a & finF b12]
  && [&& mulFv a x0 ax0, mulFv a onem b01, mulFv a x1 ax1 & mulFv a h1 ah1]
  && fastTwoSumOkb b01 b12.

Lemma reciBW_okbP x0 x1 : reciBW_okb x0 x1 = true -> reciBW_ok x0 x1.
Proof.
move=> /andP[/andP[/and3P[A2 A4 Gb12] /and4P[M0 M1 M2 M3]] Hfast].
have Fb12 := finFP _ Gb12.
have [Fb11 Fah1] := Dfin_addI _ _ Fb12.
have [Fa Fh1] := Dfin_mulI _ _ Fah1.
have [Fnh11 Fax1] := Dfin_subI _ _ Fh1.
have Fh11 := Dfin_oppI _ Fnh11.
have [Fpm Fpelo] := Dfin_addI _ _ Fh11.
have [Fpehi _] := Dfin_subI _ _ Fpm.
have [_ Fx1] := Dfin_mulI _ _ Fax1.
have [_ Fx0 _] := twoProd_finI _ _ Fpelo.
have [_ Fonem Fb01] := twoProd_finI _ _ Fb11.
have Hn : (Dnorm < Rabs (D2R (onep / x0)%float))%R by apply: normFP.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Nx0 : (D2R x0 <> 0)%R.
  have Fax : Dfin (abs x0) by apply: Dfin_abs.
  have H0 : Dfin 0%float by [].
  have E0 : D2R 0%float = 0%R by rewrite /D2R; compute; lra.
  have := Dltb _ _ H0 Fax A2; rewrite E0 D2R_abs; split_Rabs; lra.
split; first by split.
split.
  by apply: DnormT_of_rnd; have [E _] := Dfin_div _ _ Dfin_onep Nx0 Fa;
     rewrite -E.
split; first by split.
split.
  by split; apply: mulFvP.
split; first by split.
by apply: fastTwoSumOkbP.
Qed.

Definition sub2Tw_okb (t : twfloat) : bool :=
  let: TWFloat x0 x1 x2 := t in
  [&& finF x0, finF x1, finF x2 & subOkb 2 x0].

Lemma sub2Tw_okbP t : sub2Tw_okb t = true -> sub2Tw_ok t.
Proof.
case: t => x0 x1 x2 /and4P[H0 H1 H2 H3].
have F0 := finFP _ H0; have F1 := finFP _ H1; have F2 := finFP _ H2.
have F2f : Dfin 2%float by [].
have E2 : D2R 2%float = 2%R by rewrite /D2R; compute; lra.
have [E Fs] := sub_exact _ _ F2f F0 H3.
by split => //; rewrite E E2.
Qed.

Definition div_okb (z x : twfloat) : bool :=
  let bw := reciBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  let s2 := sub2Tw i1 in
  let az := threeProdDW bw z in
  [&& reciBW_okb (tw0 x) (tw1 x),
      prodDW_okb (tw0 bw) (tw1 bw) (tw0 x) (tw1 x) (tw2 x),
      prodDW_okb (tw0 bw) (tw1 bw) (tw0 z) (tw1 z) (tw2 z),
      sub2Tw_okb i1
    & prodOne_okb (tw0 az) (tw1 az) (tw2 az) (tw1 s2) (tw2 s2)].

(* THE ANSWER AND THE FLAG IN ONE PASS.  `threeDiv' and `div_okb' are the    *)
(* same four numbers read twice; here they are read once.  The pair is the    *)
(* two computed apart, which is what the lemma below says, so nothing above   *)
(* has to know about it.  This is `code/ddouble's `divDwDw2GS'.               *)
Definition reciBWG (x0 x1 : PrimFloat.float) : twfloat * bool :=
  let a := (onep / x0)%float in
  let pe := twoProd a x0 in
  let ax0 := dwhi pe in
  let pm := (ax0 - onep)%float in
  let h11 := (pm + dwlo pe)%float in
  let ax1 := (a * x1)%float in
  let h1 := (- h11 - ax1)%float in
  let bp := twoProd a onem in
  let b01 := dwhi bp in
  let b11 := dwlo bp in
  let ah1 := (a * h1)%float in
  let b12 := (b11 + ah1)%float in
  (let: DWFloat bh bl := fastTwoSum b01 b12 in TWFloat bh bl 0,
   [&& (0 <? abs x0)%float, normF a & finF b12]
   && [&& mulFv a x0 ax0, mulFv a onem b01, mulFv a x1 ax1 & mulFv a h1 ah1]
   && fastTwoSumOkb b01 b12).

Lemma reciBWGE x0 x1 : reciBWG x0 x1 = (reciBW x0 x1, reciBW_okb x0 x1).
Proof. by []. Qed.

Definition threeDivG (z x : twfloat) : twfloat * bool :=
  let: (bw, k0) := reciBWG (tw0 x) (tw1 x) in
  let: (i1, k1) := prodDWG bw x in
  let s2 := sub2Tw i1 in
  let: (az, k2) := prodDWG bw z in
  let: (q, k4) := prodOneG az s2 in
  (q, [&& k0, k1, k2, sub2Tw_okb i1 & k4]).

Lemma threeDivGE z x : threeDivG z x = (threeDiv z x, div_okb z x).
Proof.
by rewrite /threeDivG /threeDiv /div_okb reciBWGE !prodDWGE prodOneGE.
Qed.

Lemma div_okbP z x : div_okb z x = true -> div_ok z x.
Proof.
move=> /and5P[H1 H2 H3 H4 H5].
split; first by apply: reciBW_okbP.
split; first by apply: prodDW_okbP.
split; first by apply: prodDW_okbP.
split; first by apply: sub2Tw_okbP.
by apply: prodOne_okbP.
Qed.

(* ---------------------------------------------------------------------------*)
(*  What the quotient is out by, and that the step covers it                  *)
(* ---------------------------------------------------------------------------*)

Theorem threeDiv_error z x :
  div_ok z x -> isTW prec (tw2R z) -> isTW prec (tw2R x) ->
  (D2R (tw0 x) <> 0)%R ->
  (Rabs (twval (threeDiv z x) - twval z / twval x)
     <= (56 * (Xu * Xu * Xu) + 5000 * (Xu * Xu * Xu * Xu))
        * Rabs (twval z / twval x))%R.
Proof.
move=> Hok Hz Hx Hx0.
have Hp2 : (1 < prec)%Z by [].
have Hp11 : (11 <= prec)%Z by [].
have Ht0 : TWR.tw0 (tw2R x) = D2R (tw0 x) by case: x {Hok Hx Hx0}.
have H := ThreeDivN_error Hp2 Hp11 Dchoice_sym Dchoice_te Hz Hx
            (ltac:(by rewrite Ht0) : TWR.tw0 (tw2R x) <> 0%R).
rewrite -!TWval_tw2R (threeDiv_X _ _ Hok).
exact: H.
Qed.

(* Fifty-six against the sixty-four that `2^-153' makes, less what the        *)
(* leading word and the answer's own error take off: it clears with an        *)
(* eighth to spare.                                                           *)
Theorem kstep_div_ok z x :
  finL (tw2l z) -> wellFormed z = true ->
  finL (tw2l x) -> wellFormed x = true ->
  (Dnorm <= Rabs (D2R (tw0 z)))%R ->
  (D2R (tw1 z) = 0%R \/ (Dnorm <= Rabs (D2R (tw1 z)))%R) ->
  (Dnorm <= Rabs (D2R (tw0 x)))%R ->
  (D2R (tw1 x) = 0%R \/ (Dnorm <= Rabs (D2R (tw1 x)))%R) ->
  (D2R (tw0 x) <> 0)%R ->
  div_ok z x ->
  finL (tw2l (threeDiv z x)) -> wellFormed (threeDiv z x) = true ->
  (tw_updn.normLo <? abs (tw0 (threeDiv z x)))%float = true ->
  Dfin (kscale * abs (tw0 (threeDiv z x)))%float ->
  Dfin (dw_updn.mulUpFp kscale (abs (tw0 (threeDiv z x)))) ->
  (Rabs (twval (threeDiv z x) - twval z / twval x)
     <= D2R (kstep (threeDiv z x)))%R.
Proof.
move=> Fz Wz Fx Wx Hnz0 Hnz1 Hnx0 Hnx1 Hx0 Hok Fr Wr Hlo Fm Fu.
have Hz := wellFormed_isTW _ Fz Wz Hnz0 Hnz1.
have Hx := wellFormed_isTW _ Fx Wx Hnx0 Hnx1.
have Herr := threeDiv_error _ _ Hok Hz Hx Hx0.
set r := threeDiv z x in Fr Wr Hlo Fm Fu Herr *.
have Fr0 : Dfin (tw0 r).
  by move: Fr; rewrite /tw2l; case: (r) => r0 r1 r2 [].
have Far0 : Dfin (abs (tw0 r)) by apply: Dfin_abs.
have Fk : Dfin kscale by rewrite /Dfin /kscale; compute.
have Estep : D2R (kstep r) = D2R (dw_updn.mulUpFp kscale (abs (tw0 r))).
  by move: Hlo; rewrite /kstep; case: (r) => r0 r1 r2 /= ->.
have Hge : (bpow radix2 (-153) * Rabs (D2R (tw0 r)) <= D2R (kstep r))%R.
  rewrite Estep -Dkscale -D2R_abs.
  by apply: dwbound.mulUpFp_ge.
have Hn : (Dnorm <= Rabs (D2R (tw0 r)))%R.
  have Hn1 : (D2R tw_updn.normLo < Rabs (D2R (tw0 r)))%R
    by rewrite -D2R_abs; apply: Dltb.
  move: Hn1; rewrite DnormLo => Hn1.
  apply: Rle_trans (Rlt_le _ _ Hn1).
  by apply: bpow_le; rewrite /SpecFloat.emin /=; lia.
have Hlead := wellFormed_lead_tight _ Fr Wr Hn.
(* the leading word carries all but `1.5u' of the value, so it is within an   *)
(* eighth of the answer itself                                                *)
have Hv : (Rabs (twval z / twval x)
           * (1 - (56 * (Xu * Xu * Xu) + 5000 * (Xu * Xu * Xu * Xu)))
           <= Rabs (twval r))%R.
  have T := Rabs_triang_inv (twval r) (twval z / twval x).
  have T2 : (Rabs (twval z / twval x) - Rabs (twval r)
             <= Rabs (twval r - twval z / twval x))%R
    by move: T; rewrite Rabs_minus_sym; split_Rabs; lra.
  by lra.
have Eu : Xu = bpow radix2 (-53) by rewrite (u_pow prec).
have H52 : bpow radix2 (-52) = (2 * bpow radix2 (-53))%R.
  have -> : (2 = bpow radix2 1)%R by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -bpow_plus.
have H153 : bpow radix2 (-153) = (64 * (bpow radix2 (-53)
             * (bpow radix2 (-53) * bpow radix2 (-53))))%R.
  have -> : (64 = bpow radix2 6)%R by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -!bpow_plus.
have Hb53 : (0 < bpow radix2 (-53))%R by apply: bpow_gt_0.
have Hb53s : (bpow radix2 (-53) <= / 1048576)%R.
  have -> : (/ 1048576 = bpow radix2 (-20))%R
    by rewrite /= /Z.pow_pos /=; lra.
  by apply: bpow_le; lia.
have Hr0 := Rabs_pos (D2R (tw0 r)).
have Hs0 := Rabs_pos (twval z / twval x).
move: Herr Hlead Hv Hge; rewrite Eu H52 H153.
set w := bpow radix2 (-53) in Hb53 Hb53s *.
set S := Rabs (twval z / twval x) in Hs0 *.
set R0 := Rabs (D2R (tw0 r)) in Hr0 *.
move=> Herr Hlead Hv Hge.
set V := Rabs (twval r) in Hlead Hv *.
set E := (56 * (w * w * w) + 5000 * (w * w * w * w))%R in Herr Hv *.
have Ht : (0 <= w * w * w)%R by nra.
have Ht4 : (0 <= w * w * w * w)%R by nra.
have Hw2 : (w * w <= / 1048576 * w)%R by nra.
have Hw3 : (w * w * w <= / 1048576 * (w * w))%R by nra.
have Hw4 : (w * w * w * w <= / 1048576 * (w * w * w))%R by nra.
have HE0 : (0 <= E)%R by rewrite /E; lra.
have HEu : (E <= 561 / 10 * (w * w * w))%R by rewrite /E; lra.
have HEs : (E <= 1 / 100)%R by lra.
have HE1 : (0 < 1 - E)%R by lra.
have Hscal : (E * (1 + 3 * w) <= 64 * (w * w * w) * (1 - E))%R.
  have H1 : (E * (1 + 3 * w) <= 561 / 10 * (w * w * w) * (1 + 3 * w))%R
    by nra.
  have H2 : (561 / 10 * (w * w * w) * (1 + 3 * w)
             <= 64 * (w * w * w) * (99 / 100))%R by nra.
  have H3 : (64 * (w * w * w) * (99 / 100) <= 64 * (w * w * w) * (1 - E))%R
    by nra.
  lra.
have Hchain : (S * (1 - E) <= (1 + 3 * w) * R0)%R by lra.
have Hstep1 : (E * (S * (1 - E)) <= E * ((1 + 3 * w) * R0))%R by nra.
have Hstep2 : (E * ((1 + 3 * w) * R0) <= 64 * (w * w * w) * (1 - E) * R0)%R
  by nra.
have Hfin : (E * S <= 64 * (w * w * w) * R0)%R by nra.
lra.
Qed.

(* And with every hypothesis a test.                                          *)
Theorem kstep_div_testable z x :
  finL (tw2l z) -> wellFormed z = true ->
  finL (tw2l x) -> wellFormed x = true ->
  normF (tw0 z) = true -> ((tw1 z =? 0)%float || normF (tw1 z)) = true ->
  normF (tw0 x) = true -> ((tw1 x =? 0)%float || normF (tw1 x)) = true ->
  div_okb z x = true ->
  finL (tw2l (threeDiv z x)) -> wellFormed (threeDiv z x) = true ->
  (tw_updn.normLo <? abs (tw0 (threeDiv z x)))%float = true ->
  finF (kscale * abs (tw0 (threeDiv z x)))%float = true ->
  finF (dw_updn.mulUpFp kscale (abs (tw0 (threeDiv z x)))) = true ->
  (Rabs (twval (threeDiv z x) - twval z / twval x)
     <= D2R (kstep (threeDiv z x)))%R.
Proof.
move=> Fz Wz Fx Wx Hz0 Hz1 Hx0 Hx1 Hok Fr Wr Hlo Hm Hu.
have Ftz0 : Dfin (tw0 z).
  by move: Fz; rewrite /tw2l; case: (z) => z0 z1 z2 [].
have Ftz1 : Dfin (tw1 z).
  by move: Fz; rewrite /tw2l; case: (z) => z0 z1 z2 [_ []].
have Ftx0 : Dfin (tw0 x).
  by move: Fx; rewrite /tw2l; case: (x) => x0 x1 x2 [].
have Ftx1 : Dfin (tw1 x).
  by move: Fx; rewrite /tw2l; case: (x) => x0 x1 x2 [_ []].
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Hnx0 := normFP _ Ftx0 Hx0.
apply: kstep_div_ok => //.
- by have := normFP _ Ftz0 Hz0; lra.
- case/orP: Hz1 => [Hzz|Hn]; first by left; have [] := Dfin_eqb0 _ Hzz.
  by right; have := normFP _ Ftz1 Hn; lra.
- by lra.
- case/orP: Hx1 => [Hzz|Hn]; first by left; have [] := Dfin_eqb0 _ Hzz.
  by right; have := normFP _ Ftx1 Hn; lra.
- by move: Hnx0; split_Rabs; lra.
- by apply: div_okbP.
- by apply: finFP.
by apply: finFP.
Qed.
