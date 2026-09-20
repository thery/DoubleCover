From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith Require Import twarith twbound tw_updn twpaper twflx twdivflx.
From dwarith Require Import dwbridge dwtwosum dwprod dwflx.

(* THE QUOTIENT, WITH ITS GUARD TESTED.                                       *)
(*                                                                            *)
(* `twpaper.v' assumed `kstep_div': the step the answer is widened by covers  *)
(* what Algorithm 14 is out by.  It no longer has to.  `twdivflx.v' proves    *)
(* `kstep_div_testable' -- the same statement with every hypothesis a boolean *)
(* -- so the operation tests them and the bound follows.  Where the test      *)
(* fails the answer is `nan', which an interval library reads as no           *)
(* information and is always sound.                                           *)

Open Scope float_scope.

(* Everything `kstep_div_testable' asks that the operation can see.           *)
Definition divOkT (z x : twfloat) : bool :=
  let q := threeDiv z x in
  [&& normF (tw0 z), ((tw1 z =? 0)%float || normF (tw1 z)),
      normF (tw0 x) & ((tw1 x =? 0)%float || normF (tw1 x))]
  && [&& div_okb z x, wellFormed q,
         (tw_updn.normLo <? abs (tw0 q))%float,
         finF (kscale * abs (tw0 q))%float
       & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))].

Definition divTwUpQ (z x : twfloat) :=
  if posFp (magDnTw x) && divOkT z x
  then shiftUp (threeDiv z x) else TWFloat nan nan nan.

Definition divTwDnQ (z x : twfloat) :=
  if posFp (magDnTw x) && divOkT z x
  then shiftDn (threeDiv z x) else TWFloat nan nan nan.

Open Scope R_scope.

Lemma divOkT_step z x :
  finL (tw2l z) -> wellFormed z = true ->
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (threeDiv z x)) -> divOkT z x = true ->
  (Rabs (twval (threeDiv z x) - twval z / twval x)
     <= D2R (kstep (threeDiv z x)))%R.
Proof.
move=> Fz Wz Fx Wx Fq /andP[/and4P[H0 H1 H2 H3] /and5P[H4 H5 H6 H7 H8]].
by apply: kstep_div_testable.
Qed.

Lemma divTwUpQ_nz x y : finL (tw2l (divTwUpQ x y)) -> twval y <> (0 : R).
Proof.
rewrite /divTwUpQ; case Hp: (posFp (magDnTw y) && divOkT x y);
  last by move/finL_nan3.
by have [H _] := andb_prop _ _ Hp; move=> _; apply: divGuard_nz.
Qed.

Lemma divTwDnQ_nz x y : finL (tw2l (divTwDnQ x y)) -> twval y <> (0 : R).
Proof.
rewrite /divTwDnQ; case Hp: (posFp (magDnTw y) && divOkT x y);
  last by move/finL_nan3.
by have [H _] := andb_prop _ _ Hp; move=> _; apply: divGuard_nz.
Qed.

Theorem divTwUpQ_ge x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwUpQ x y)) ->
  (twval x / twval y <= twval (divTwUpQ x y))%R.
Proof.
move=> Fx Wx Fy Wy; rewrite /divTwUpQ.
case Hp: (posFp (magDnTw y) && divOkT x y); last by move/finL_nan3.
have [_ Hok] := andb_prop _ _ Hp.
rewrite /shiftUp => Fw.
have [Fq Fk] := widenUp_finI _ _ Fw.
have Hw := widenUp_ge _ _ Fw.
have Hk := divOkT_step _ _ Fx Wx Fy Wy Fq Hok.
by move: Hw Hk; split_Rabs; lra.
Qed.

Theorem divTwDnQ_le x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwDnQ x y)) ->
  (twval (divTwDnQ x y) <= twval x / twval y)%R.
Proof.
move=> Fx Wx Fy Wy; rewrite /divTwDnQ.
case Hp: (posFp (magDnTw y) && divOkT x y); last by move/finL_nan3.
have [_ Hok] := andb_prop _ _ Hp.
rewrite /shiftDn => Fw.
have [Fq Fk] := widenDn_finI _ _ Fw.
have Hw := widenDn_le _ _ Fw.
have Hk := divOkT_step _ _ Fx Wx Fy Wy Fq Hok.
by move: Hw Hk; split_Rabs; lra.
Qed.

(* What it computes.                                                          *)
Compute (divTwDnQ (fp2tw 1) (fp2tw 3), divTwUpQ (fp2tw 1) (fp2tw 3)).
Compute (divTwDnQ (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40),
         divTwUpQ (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40)).
