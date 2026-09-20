From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith Require Import twarith twbound tw_updn twpaper twflx.
From dwarith Require Import dwbridge dwtwosum dwprod dwflx.

(* THE ROOT, WITH ITS GUARD TESTED.                                          *)
(*                                                                            *)
(* `twpaper.v' assumes `kstep_div': the step the quotient is widened by       *)
(* covers what Algorithm 16 is out by.  It assumed the same of the root, and  *)
(* no longer has to.  `twflx.v' proves `kstep_sqrt_testable' -- the same      *)
(* statement with every hypothesis a boolean -- so the operation tests them   *)
(* and the bound follows.  What the test rules out is a product inside the    *)
(* algorithm underflowing, or Dekker's own splitting overflowing at the top   *)
(* of the range; where it fails the answer is `nan', which an interval        *)
(* library reads as `no information' and is always sound.                     *)

Open Scope float_scope.

(* Everything `kstep_sqrt_testable' asks that the operation can see.          *)
Definition sqrtOkT (x : twfloat) : bool :=
  let q := threeSqRt x in
  [&& normF (tw0 x), ((tw1 x =? 0)%float || normF (tw1 x)), sqrt_okb x,
      wellFormed q
    & [&& (tw_updn.normLo <? abs (tw0 q))%float,
          finF (kscale * abs (tw0 q))%float
        & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))]].

(* The root of a negative number is taken to be nought here, so a bound      *)
(* below it would be a claim about nothing: what it is given has to be above  *)
(* zero, and so has the answer, which is what the shift is taken from.        *)
Definition sqrtTwUpP (x : twfloat) :=
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp ((tw0 x + tw1 x + tw2 x)%float) && sqrtOkT x
  then shiftUp q else TWFloat nan nan nan.

Definition sqrtTwDnP (x : twfloat) :=
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp ((tw0 x + tw1 x + tw2 x)%float) && sqrtOkT x
  then shiftDn q else TWFloat nan nan nan.

Open Scope R_scope.

Lemma sqrtOkT_step x :
  finL (tw2l x) -> wellFormed x = true -> (0 < twval x)%R ->
  finL (tw2l (threeSqRt x)) -> sqrtOkT x = true ->
  (Rabs (twval (threeSqRt x) - R_sqrt.sqrt (twval x))
     <= D2R (kstep (threeSqRt x)))%R.
Proof.
move=> Fl Ew Hx Fq /and5P[H0 H1 H2 H3 /and3P[H4 H5 H6]].
by apply: kstep_sqrt_testable.
Qed.

Theorem sqrtTwUpP_ge x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwUpP x)) ->
  (R_sqrt.sqrt (twval x) <= twval (sqrtTwUpP x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwUpP.
case Hp: (posFp (valDnTw (threeSqRt x))
          && posFp ((tw0 x + tw1 x + tw2 x)%float) && sqrtOkT x);
  last by move/finL_nan3.
have [/andP[_ Hs] Hok] := andb_prop _ _ Hp.
rewrite /shiftUp => Fw.
have [Fq Fk] := widenUp_finI _ _ Fw.
have Hw := widenUp_ge _ _ Fw.
have Hx : (0 < twval x)%R.
  by apply: sqrtGuard_pos => //; move: Hs; case: (x).
have Hk := sqrtOkT_step _ Fl Ew Hx Fq Hok.
by move: Hw Hk; split_Rabs; lra.
Qed.

Theorem sqrtTwDnP_le x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwDnP x)) ->
  (twval (sqrtTwDnP x) <= R_sqrt.sqrt (twval x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwDnP.
case Hp: (posFp (valDnTw (threeSqRt x))
          && posFp ((tw0 x + tw1 x + tw2 x)%float) && sqrtOkT x);
  last by move/finL_nan3.
have [/andP[_ Hs] Hok] := andb_prop _ _ Hp.
rewrite /shiftDn => Fw.
have [Fq Fk] := widenDn_finI _ _ Fw.
have Hw := widenDn_le _ _ Fw.
have Hx : (0 < twval x)%R.
  by apply: sqrtGuard_pos => //; move: Hs; case: (x).
have Hk := sqrtOkT_step _ Fl Ew Hx Fq Hok.
by move: Hw Hk; split_Rabs; lra.
Qed.

(* What it computes.                                                          *)
Compute (sqrtTwDnP (fp2tw 2), sqrtTwUpP (fp2tw 2)).
