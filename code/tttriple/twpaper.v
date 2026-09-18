From mathcomp Require Import all_ssreflect.
From Stdlib Require Import ZArith Reals Psatz.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
Require Import PrimInt63 Floats.
From dwarith Require Import dwbridge dwbound.
From twarith Require Import twarith tw_updn twbound.

(* The paper's own algorithms, on primitive floats.                          *)
(*                                                                           *)
(* `twarith.v' has algorithms of my own for the quotient and the root - a     *)
(* long division and Newton's method - chosen because the bound that went     *)
(* with them was a residual, and a residual asks nothing of the algorithm it  *)
(* is handed.  Bounding by a shift of so many units in the last place asks    *)
(* the opposite: the number of units has to come from a theorem about the     *)
(* algorithm, and the theorems there are about the paper's algorithms.  So    *)
(* these are the paper's, and `threewords/' holds their proofs.               *)
(*                                                                           *)
(* ONE CHANGE THROUGHOUT, and it is forced: Rocq's primitive floats have no   *)
(* fused multiply-add.  Every step the paper writes as one rounding of        *)
(* `a + b * c' is two roundings here, and every product error that the paper  *)
(* takes from an FMA is taken from the two-product instead.  The paper's      *)
(* constants therefore do not carry over as they stand; measured on random    *)
(* inputs, the quotient below is out by 2.3 units in the last place where     *)
(* the paper's own is out by less, and eight covers it.                       *)
(*                                                                           *)
(* WHAT IS PROVED HERE AND WHAT IS ASSUMED.  The algorithms themselves are    *)
(* transcriptions and nothing is proved of them.  The SIZE OF THE STEP is     *)
(* stated below as two assumptions in their own right -- `kstep_div' and      *)
(* `kstep_sqrt' -- rather than left hiding inside the four obligations of     *)
(* `tw_ops.v'.  They are the only thing here that is measured rather than     *)
(* proved, and `Print Assumptions' on anything that leans on the quotient or  *)
(* the root names them.  Everything between them and the obligations -- the   *)
(* guards, the widening, the reading into Interval's shape -- is proved.      *)

Implicit Type t : twfloat.

(* The Fast2Sum that puts its arguments the right way round first.            *)
Definition fast2SumS (a b : float) :=
  if (abs b <=? abs a)%float then fastTwoSum a b else fastTwoSum b a.

(* The first three of a list, filled out with noughts.                        *)
Definition nth3 (l : seq float) :=
  (nth 0%float l 0, nth 0%float l 1, nth 0%float l 2).

(* ===========================================================================*)
(*  Algorithm 11 - a double word times a triple word                          *)
(* ===========================================================================*)

Definition threeProdDW (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 _ := x in
  let: TWFloat y0 y1 y2 := y in
  let: DWFloat z00p z00m := twoProd x0 y0 in
  let: DWFloat z01p z01m := twoProd x0 y1 in
  let: DWFloat z10p z10m := twoProd x1 y0 in
  let: (b0, b1, b2) := nth3 (vecSum [:: z00m; z01p; z10p]) in
  let c   := (b2 + x1 * y1)%float in
  let z31 := (z10m + x0 * y2)%float in
  let z3  := (z31 + z01m)%float in
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0%float e 0 in
  l2tw (e0 :: take 2 (vseb [:: nth 0%float e 1; nth 0%float e 2;
                              nth 0%float e 3; nth 0%float e 4])).

(* ===========================================================================*)
(*  Algorithms 18 and 20 - the second argument has leading word one           *)
(* ===========================================================================*)

(* The part the two share.                                                    *)
Definition p18head (x0 x1 y1 y2 : float) : float * float :=
  let: DWFloat z01p z01m := twoProd x0 y1 in
  let: DWFloat bh bl := fast2SumS x1 z01p in
  let z31 := (z01m + x1 * y1)%float in
  let z3  := (z31 + x0 * y2)%float in
  (bh, (bl + z3)%float).

(* Algorithm 18: a double word times a triple word whose leading word is one. *)
Definition threeProdOne (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 _ := x in
  let: TWFloat _ y1 y2 := y in
  let: (bh, s3) := p18head x0 x1 y1 y2 in
  let: (e0, e1, e2) := nth3 (vecSum [:: x0; bh; s3]) in
  let: DWFloat r1 r2 := fast2SumS e1 e2 in
  TWFloat e0 r1 r2.

(* Algorithm 20: the same with a triple word on the left.                     *)
Definition threeProdOneTW (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat _ y1 y2 := y in
  let: (bh, s3) := p18head x0 x1 y1 y2 in
  let: (e0, e1, e2) := nth3 (vecSum [:: x0; bh; (s3 + x2)%float]) in
  let: DWFloat r1 r2 := fast2SumS e1 e2 in
  TWFloat e0 r1 r2.

(* ===========================================================================*)
(*  Algorithm 13's head - the Newton double word for the reciprocal           *)
(* ===========================================================================*)

(* Two to the minus fifty-third, the unit roundoff.                           *)
Definition uu := Eval compute in 0x1p-53%float.

(* One plus two of them is the float just above one, which is what makes      *)
(* the rounded product of it with the reciprocal come back exactly - the      *)
(* fact the whole of Algorithm 13 rests on.                                   *)
Definition onep := Eval compute in (1 + 2 * 0x1p-53)%float.
Definition onem := Eval compute in (1 - 2 * 0x1p-53)%float.

Definition reciBW (x0 x1 : float) : twfloat :=
  let a := (onep / x0)%float in
  (* the paper's FMA `RN(a x0 - (1 + 2u))', done with the two-product        *)
  let: DWFloat p e := twoProd a x0 in
  let h11 := ((p - onep) + e)%float in
  let h1  := (- h11 - a * x1)%float in
  let: DWFloat b01 b11 := twoProd a onem in
  let b12 := (b11 + a * h1)%float in
  let: DWFloat bh bl := fastTwoSum b01 b12 in
  TWFloat bh bl 0.

(* Two less a triple word, which is exact on every word.                      *)
Definition sub2Tw t :=
  let: TWFloat x0 x1 x2 := t in TWFloat (2 - x0)%float (- x1)%float (- x2)%float.

(* ===========================================================================*)
(*  Algorithms 13 and 14 - the reciprocal and the quotient                    *)
(* ===========================================================================*)

Definition threeReci (x : twfloat) : twfloat :=
  let bw := reciBW (tw0 x) (tw1 x) in
  threeProdOne bw (sub2Tw (threeProdDW bw x)).

Definition threeDiv (z x : twfloat) : twfloat :=
  let bw := reciBW (tw0 x) (tw1 x) in
  threeProdOneTW (threeProdDW bw z) (sub2Tw (threeProdDW bw x)).

(* ===========================================================================*)
(*  Algorithm 15 - the square root                                            *)
(* ===========================================================================*)

(* One and four of the unit roundoff.  It plays for the root the part one     *)
(* plus two of them plays for the reciprocal: it tilts the seed up by just     *)
(* enough that the rounding in the middle cannot go the wrong way.            *)
Definition onep4 := Eval compute in (1 + 4 * 0x1p-53)%float.
Definition three2 := Eval compute in (3 / 2)%float.

(* The Newton double word for one over the root.  The three steps the paper   *)
(* writes with a fused multiply-add are two roundings each.                    *)
Definition sqrtBW (x0 x1 : float) : twfloat :=
  let s := PrimFloat.sqrt x0 in
  let a := (onep4 / s)%float in
  let a' := (a / 2)%float in
  let: DWFloat h01_1 h11_1 := twoProd a x0 in
  let h1_1 := (h11_1 + a * x1)%float in
  let: DWFloat h01_2 h11_2 := twoProd a' h01_1 in
  let h0_2 := (three2 - h01_2)%float in
  let h1_2 := (- (h11_2 + a' * h1_1))%float in
  let: DWFloat b01 b11 := twoProd a h0_2 in
  let b12 := (b11 + a * h1_2)%float in
  let: DWFloat bh bl := fastTwoSum b01 b12 in
  TWFloat bh bl 0.

(* Three halves less a triple word, exact on every word once the leading      *)
(* word is a half - which is what the middle product is for.                  *)
Definition sub32Tw t :=
  let: TWFloat x0 x1 x2 := t in
  TWFloat (three2 - x0)%float (- x1)%float (- x2)%float.

Definition threeSqRt (x : twfloat) : twfloat :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  threeProdOneTW i1 (sub32Tw (threeProdDW (halfTw bw) i1)).

(* ===========================================================================*)
(*  The bounds: the answer shifted so many units in the last place            *)
(* ===========================================================================*)

(* MEASURED, on forty thousand random triple words, in units of the last      *)
(* place of the third word: the sum is out by 0.9, Algorithm 9 by 1.7,         *)
(* Algorithm 11 by 1.7 and Algorithm 14 by 2.3.  Eight covers all of them,     *)
(* and eight units of a word that sits a hundred and fifty-nine bits below    *)
(* the leading one is the leading one shifted down a hundred and fifty-six.    *)
(* The probing is `probek.py' beside this file.                                *)
(*                                                                            *)
(* ADMITTED, not proved.  The number comes from running the algorithms, not    *)
(* from their theorems: the theorems are in `threewords/' but they are about   *)
(* the paper's steps, and the FMA is not available here.                       *)
Definition kscale := Eval compute in 0x1p-156%float.

(* The paper's bounds hold in the NORMAL range only - they are proved in the  *)
(* format with no smallest exponent.  Below that the shift would be a claim    *)
(* about nothing, so the bottom of the range gets a fixed step instead, which  *)
(* needs no error analysis: down there every number is a whole multiple of     *)
(* the smallest float and an operation can only be out by one of those.  The   *)
(* fixed step covers the shifted one at the line, and the shifted one only     *)
(* gets smaller below it, so the same step serves all the way down.            *)
Definition kstep t :=
  let: TWFloat x0 _ _ := t in
  if (normLo <? abs x0)%float then mulUpFp kscale (abs x0) else tabs.

(* The sweep is kept.  Not for the step - it is far too small to disturb the  *)
(* words - but because a seed need not be a triple word at all, and the       *)
(* sweep is what makes it one.                                                 *)
Definition shiftUp t := widenUp t (kstep t).
Definition shiftDn t := widenDn t (kstep t).

(* A number is a usable divisor when it is above zero and not an infinity.    *)
Definition divTwUpP (x y : twfloat) :=
  if posFp (magDnTw y) then shiftUp (threeDiv x y) else TWFloat nan nan nan.
Definition divTwDnP (x y : twfloat) :=
  if posFp (magDnTw y) then shiftDn (threeDiv x y) else TWFloat nan nan nan.

(* The root of a negative number is taken to be nought here, so a bound      *)
(* below it would be a claim about nothing: what it is given has to be above  *)
(* zero, and so has the answer, which is what the shift is taken from.        *)
Definition sqrtTwUpP (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then shiftUp q else TWFloat nan nan nan.
Definition sqrtTwDnP (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then shiftDn q else TWFloat nan nan nan.

(* ===========================================================================*)
(*  The step, assumed; the four bounds, proved from it                        *)
(* ===========================================================================*)

(* THESE TWO ARE MEASURED, NOT PROVED, and they are the whole of what is.     *)
(* `probek.py' beside this file runs the two algorithms on forty thousand     *)
(* random triple words and reports how far out they are in units of the last  *)
(* place of the third word: the quotient by 2.3 and the root by less.  Eight  *)
(* units is what `kscale' allows, and `kstep' turns that into a step down     *)
(* from the leading word, with a fixed step below the normal range where the  *)
(* paper's own bounds say nothing.                                            *)
(*                                                                            *)
(* They are stated of the ANSWER's own step, `kstep (threeDiv x y)', because  *)
(* that is what the operation adds; and with the divisor kept away from       *)
(* nought and the number under the root kept above it, because outside that   *)
(* neither algorithm is asked for anything.                                   *)
Axiom kstep_div : forall x y,
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  twval y <> 0%R ->
  finL (tw2l (threeDiv x y)) ->
  (Rabs (twval (threeDiv x y) - twval x / twval y)
     <= D2R (kstep (threeDiv x y)))%R.

Axiom kstep_sqrt : forall x,
  finL (tw2l x) -> wellFormed x = true ->
  (0 < twval x)%R ->
  finL (tw2l (threeSqRt x)) ->
  (Rabs (twval (threeSqRt x) - R_sqrt.sqrt (twval x))
     <= D2R (kstep (threeSqRt x)))%R.

(* Nothing the guards turn away is a number, so the four bounds below have    *)
(* nothing to say about it.                                                   *)
Lemma finL_nan3 : finL (tw2l (TWFloat nan nan nan)) -> False.
Proof. by case. Qed.

(* The divisor is kept away from nought by its own guard.                     *)
Lemma divGuard_nz y : posFp (magDnTw y) = true -> twval y <> 0%R.
Proof.
move=> Hp; have [Fm Hm] := posFpP _ Hp.
have Hle := magDnTw_le _ Fm.
by move=> H0; move: Hle Hm; rewrite H0 Rabs_R0; lra.
Qed.

(* The guard is not merely tested, it is recoverable: the answer's words are  *)
(* numbers only if the guard let it through.                                  *)
Lemma divTwUpP_nz x y : finL (tw2l (divTwUpP x y)) -> twval y <> 0%R.
Proof.
rewrite /divTwUpP; case Hp: (posFp (magDnTw y)); last by move/finL_nan3.
by move=> _; apply: divGuard_nz.
Qed.

Lemma divTwDnP_nz x y : finL (tw2l (divTwDnP x y)) -> twval y <> 0%R.
Proof.
rewrite /divTwDnP; case Hp: (posFp (magDnTw y)); last by move/finL_nan3.
by move=> _; apply: divGuard_nz.
Qed.

Theorem divTwUpP_ge x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwUpP x y)) ->
  (twval x / twval y <= twval (divTwUpP x y))%R.
Proof.
move=> Fx Wx Fy Wy; rewrite /divTwUpP.
case Hp: (posFp (magDnTw y)); last by move/finL_nan3.
rewrite /shiftUp => Fw.
have [Fq Fk] := widenUp_finI _ _ Fw.
have Hw := widenUp_ge _ _ Fw.
have Hk := kstep_div _ _ Fx Wx Fy Wy (divGuard_nz _ Hp) Fq.
by move: Hw Hk; split_Rabs; lra.
Qed.

Theorem divTwDnP_le x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwDnP x y)) ->
  (twval (divTwDnP x y) <= twval x / twval y)%R.
Proof.
move=> Fx Wx Fy Wy; rewrite /divTwDnP.
case Hp: (posFp (magDnTw y)); last by move/finL_nan3.
rewrite /shiftDn => Fw.
have [Fq Fk] := widenDn_finI _ _ Fw.
have Hw := widenDn_le _ _ Fw.
have Hk := kstep_div _ _ Fx Wx Fy Wy (divGuard_nz _ Hp) Fq.
by move: Hw Hk; split_Rabs; lra.
Qed.

(* The number under the root is kept above nought by its own guard, and that  *)
(* takes a word about a triple word: being one, the first addition drops the  *)
(* second word, so what the guard tests is the first word and the third, and  *)
(* the third is at most a quarter of the first.                               *)
Lemma sqrtGuard_pos x : finL (tw2l x) -> wellFormed x = true ->
  posFp ((tw0 x + tw1 x + tw2 x)%float) = true -> (0 < twval x)%R.
Proof.
move=> Fl Ew Hp; have [Fs Hs] := posFpP _ Hp.
apply: wellFormed_posV => //; apply: wellFormed_pos02 => //.
move: Fl Ew Fs Hs; case: x {Hp} => x0 x1 x2 [F0 [F1 [F2 _]]] /=.
rewrite /wellFormed => /andb_prop [E1 _] Fs Hs.
have E01 := D2R_wf _ _ F0 F1 E1.
have F01 := Dfin_wf _ _ F0 E1.
have [Es _] := Dfin_add _ _ F01 F2 Fs.
move: Hs; rewrite Es E01 => Hs.
have Vr : Valid_rnd (round_mode mode_NE) by apply: valid_rnd_round_mode.
have Ve : Valid_exp Dfexp by apply: FLT_exp_valid.
case: (Rle_lt_dec (D2R x0 + D2R x2) 0) => // Hle.
have : (Drnd (D2R x0 + D2R x2) <= Drnd 0)%R by apply: round_le.
by rewrite round_0; lra.
Qed.

Theorem sqrtTwUpP_ge x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwUpP x)) ->
  (R_sqrt.sqrt (twval x) <= twval (sqrtTwUpP x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwUpP.
case: x Fl Ew => x0 x1 x2 Fl Ew.
case Hp: (posFp (valDnTw (threeSqRt (TWFloat x0 x1 x2)))
          && posFp ((x0 + x1 + x2)%float)); last by move/finL_nan3.
have [_ Hs] := andb_prop _ _ Hp.
rewrite /shiftUp => Fw.
have [Fq Fk] := widenUp_finI _ _ Fw.
have Hw := widenUp_ge _ _ Fw.
have Hx := sqrtGuard_pos _ Fl Ew Hs.
have Hk := kstep_sqrt _ Fl Ew Hx Fq.
by move: Hw Hk; split_Rabs; lra.
Qed.

Theorem sqrtTwDnP_le x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwDnP x)) ->
  (twval (sqrtTwDnP x) <= R_sqrt.sqrt (twval x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwDnP.
case: x Fl Ew => x0 x1 x2 Fl Ew.
case Hp: (posFp (valDnTw (threeSqRt (TWFloat x0 x1 x2)))
          && posFp ((x0 + x1 + x2)%float)); last by move/finL_nan3.
have [_ Hs] := andb_prop _ _ Hp.
rewrite /shiftDn => Fw.
have [Fq Fk] := widenDn_finI _ _ Fw.
have Hw := widenDn_le _ _ Fw.
have Hx := sqrtGuard_pos _ Fl Ew Hs.
have Hk := kstep_sqrt _ Fl Ew Hx Fq.
by move: Hw Hk; split_Rabs; lra.
Qed.

(* ===========================================================================*)
(*  What they compute                                                         *)
(* ===========================================================================*)

Compute threeDiv (fp2tw 1) (fp2tw 3).
Compute timesTwTw (threeDiv (fp2tw 1) (fp2tw 3)) (fp2tw 3).
Compute threeReci (fp2tw 3).
Compute threeDiv (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40).
Compute (divTwDnP (fp2tw 1) (fp2tw 3), divTwUpP (fp2tw 1) (fp2tw 3)).
Compute threeSqRt (fp2tw 2).
Compute timesTwTw (threeSqRt (fp2tw 2)) (threeSqRt (fp2tw 2)).
Compute (sqrtTwDnP (fp2tw 2), sqrtTwUpP (fp2tw 2)).
