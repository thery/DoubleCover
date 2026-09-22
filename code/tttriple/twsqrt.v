From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith Require Import twarith twbound tw_updn twpaper twflx.
From dwarith Require Import dwbridge dwtwosum dwprod dwflx dwsqrt.

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
(* IN ONE PASS.  Written as above, the root is worked out three times: once *)
(* for `sqrtOkT', once for `sqrt_okb' under it, and once for the answer.     *)
(* `threeSqRtG' does it once, and the two lemmas below say the pair is the   *)
(* two computed apart, so no proof has to look at the arrangement.           *)
Definition sqrtTwUpP (x : twfloat) :=
  let: (q, ok) := threeSqRtG x in
  if posFp (valDnTw q) && posFp ((tw0 x + tw1 x + tw2 x)%float)
     && [&& normF (tw0 x), ((tw1 x =? 0)%float || normF (tw1 x)), ok,
             wellFormed q
           & [&& (tw_updn.normLo <? abs (tw0 q))%float,
                 finF (kscale * abs (tw0 q))%float
               & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))]]
  then shiftUp q else TWFloat nan nan nan.

Definition sqrtTwDnP (x : twfloat) :=
  let: (q, ok) := threeSqRtG x in
  if posFp (valDnTw q) && posFp ((tw0 x + tw1 x + tw2 x)%float)
     && [&& normF (tw0 x), ((tw1 x =? 0)%float || normF (tw1 x)), ok,
             wellFormed q
           & [&& (tw_updn.normLo <? abs (tw0 q))%float,
                 finF (kscale * abs (tw0 q))%float
               & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))]]
  then shiftDn q else TWFloat nan nan nan.

Lemma sqrtTwUpPE x :
  sqrtTwUpP x =
  (if posFp (valDnTw (threeSqRt x)) && posFp ((tw0 x + tw1 x + tw2 x)%float)
      && sqrtOkT x
   then shiftUp (threeSqRt x) else TWFloat nan nan nan).
Proof. by rewrite /sqrtTwUpP /sqrtOkT threeSqRtGE. Qed.

Lemma sqrtTwDnPE x :
  sqrtTwDnP x =
  (if posFp (valDnTw (threeSqRt x)) && posFp ((tw0 x + tw1 x + tw2 x)%float)
      && sqrtOkT x
   then shiftDn (threeSqRt x) else TWFloat nan nan nan).
Proof. by rewrite /sqrtTwDnP /sqrtOkT threeSqRtGE. Qed.

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
move=> Fl Ew; rewrite sqrtTwUpPE.
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
move=> Fl Ew; rewrite sqrtTwDnPE.
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


(* ---------------------------------------------------------------------------*)
(*  When the guard fails, the number is moved into the band                   *)
(* ---------------------------------------------------------------------------*)

(* WHERE THE GUARD HOLDS, MEASURED.  `sqrtOkT' comes out true for a leading   *)
(* word from about two to the minus nine hundred and sixty-nine up to about   *)
(* two to the nine hundred and ninety-six, and false outside that.  The two   *)
(* ends fail for different reasons.                                           *)
(*                                                                            *)
(* At the top it is Dekker's splitting inside the two-product, which takes a  *)
(* word up by two to the twenty-seven plus one and so reaches infinity a      *)
(* little below two to the nine hundred and ninety-seven: `0x1p+996' passes   *)
(* and `0x1.fffffffffffffp+996' does not.                                     *)
(*                                                                            *)
(* At the bottom it is the step, which is a proportion of the leading word    *)
(* and so wants it above the smallest normal number; and for a triple word    *)
(* the second word sits fifty-three bits below the first, so the first has to *)
(* stay above two to the minus nine hundred and sixty-nine for the second to  *)
(* be a normal number at all.  A leading word alone, with two zero words      *)
(* after it, goes down to just above two to the minus one thousand and        *)
(* twenty-two, the test being a strict one.                                   *)
(*                                                                            *)
(* SO ONE SCALE SERVES BOTH WAYS, and it is two to the hundred and sixty:     *)
(* the failing bottom, everything under two to the minus nine hundred and     *)
(* sixty-nine, lands between two to the minus nine hundred and fourteen and   *)
(* two to the minus eight hundred and nine; the failing top, everything over  *)
(* two to the nine hundred and ninety-five, lands between two to the eight    *)
(* hundred and thirty-five and two to the eight hundred and sixty-four.  Both *)
(* are well inside.  A hundred and sixty is even, which is what lets the      *)
(* answer come back by half of it.                                            *)
Definition tsqup := Eval compute in 0x1p+160%float.
Definition tsqdn := Eval compute in 0x1p-160%float.
Definition tsqhi := Eval compute in 0x1p+80%float.
Definition tsqlo := Eval compute in 0x1p-80%float.

Lemma D2R_tsqup : D2R tsqup = bpow radix2 160.
Proof. by rewrite /D2R /tsqup; compute; lra. Qed.

Lemma D2R_tsqhi : D2R tsqhi = bpow radix2 80.
Proof. by rewrite /D2R /tsqhi; compute; lra. Qed.

Lemma Dfin_tsqup : Dfin tsqup.
Proof. by []. Qed.

Lemma Dfin_tsqhi : Dfin tsqhi.
Proof. by []. Qed.

(* A triple word scaled word by word, and the two things the operation has to *)
(* see for itself: that the three words are numbers at all, which no          *)
(* comparison says, and that the scaling lost nothing.                        *)
Definition scaleTw (t : twfloat) (s : PrimFloat.float) :=
  let: TWFloat a b c := t in TWFloat (a * s) (b * s) (c * s).

Definition finTwb (t : twfloat) :=
  let: TWFloat a b c := t in [&& finF a, finF b & finF c].

Definition scaleOkb (t : twfloat) (s sI : PrimFloat.float) :=
  let: TWFloat a b c := t in
  [&& ((a * s) * sI =? a)%float, ((b * s) * sI =? b)%float
    & ((c * s) * sI =? c)%float].

Lemma finTwbP t : finTwb t = true -> finL (tw2l t).
Proof.
case: t => a b c /and3P[Ha Hb Hc].
by split; [apply: finFP | split; [apply: finFP | split; [apply: finFP |]]].
Qed.

(* Scaling up is exact while it stays in the range, so the way back says what *)
(* the way down did: a word that comes back is a word whose scaling lost      *)
(* nothing.  Scaling down is what has to be tested, scaling up is not.        *)
Lemma scale_dn_exactT a s sI e :
  Dfin sI -> D2R sI = bpow radix2 e -> (0 <= e)%Z ->
  Dfin a -> ((a * s) * sI =? a)%float = true ->
  Dfin (a * s)%float /\ (D2R (a * s)%float * bpow radix2 e = D2R a)%R.
Proof.
move=> FsI HsI He Fa Ht.
have Ft := Deqb_fin _ _ Fa Ht.
have [Fas _] := Dfin_mulI _ _ Ft.
have Ee := Deqb_eq _ _ Ft Fa Ht.
by rewrite (mul_pow_exact _ _ _ FsI HsI He Fas Ft) in Ee.
Qed.

Lemma twval_scale_dnT t s sI e :
  Dfin sI -> D2R sI = bpow radix2 e -> (0 <= e)%Z ->
  finL (tw2l t) -> scaleOkb t s sI = true ->
  finL (tw2l (scaleTw t s)) /\
  (twval (scaleTw t s) * bpow radix2 e = twval t)%R.
Proof.
case: t => a b c.
move=> FsI HsI He [Fa [Fb [Fc _]]] /and3P[Ha Hb Hc].
have [Fas Ea] := scale_dn_exactT _ _ _ _ FsI HsI He Fa Ha.
have [Fbs Eb] := scale_dn_exactT _ _ _ _ FsI HsI He Fb Hb.
have [Fcs Ec] := scale_dn_exactT _ _ _ _ FsI HsI He Fc Hc.
split; first by split; [|split; [|split]].
by rewrite /twval /=; lra.
Qed.

Lemma twval_scale_upT t s e :
  Dfin s -> D2R s = bpow radix2 e -> (0 <= e)%Z ->
  finL (tw2l t) -> finL (tw2l (scaleTw t s)) ->
  (twval (scaleTw t s) = twval t * bpow radix2 e)%R.
Proof.
case: t => a b c.
move=> Fs Hs He [Fa [Fb [Fc _]]] [Fas [Fbs [Fcs _]]].
by apply: twval_scale.
Qed.

(* THE TWO OPERATIONS.  The direct call first; then the number taken up, for  *)
(* a number too small; then brought down, for one too large.  Each way is     *)
(* tested, and what is behind all three is `nan', so the operation is total.  *)
Definition sqrtTwUpK (x : twfloat) :=
  let q := sqrtTwUpP x in
  if finTwb q then q else
  let xu := scaleTw x tsqup in
  let qu := sqrtTwUpP xu in
  if [&& posFp ((tw0 x + tw1 x + tw2 x)%float), finTwb xu, wellFormed xu,
         finTwb qu & scaleOkb qu tsqlo tsqhi]
  then scaleTw qu tsqlo else
  let xd := scaleTw x tsqdn in
  let qd := sqrtTwUpP xd in
  if [&& posFp ((tw0 x + tw1 x + tw2 x)%float), scaleOkb x tsqdn tsqup,
         wellFormed xd & finTwb qd]
  then scaleTw qd tsqhi else TWFloat nan nan nan.

Definition sqrtTwDnK (x : twfloat) :=
  let q := sqrtTwDnP x in
  if finTwb q then q else
  let xu := scaleTw x tsqup in
  let qu := sqrtTwDnP xu in
  if [&& posFp ((tw0 x + tw1 x + tw2 x)%float), finTwb xu, wellFormed xu,
         finTwb qu & scaleOkb qu tsqlo tsqhi]
  then scaleTw qu tsqlo else
  let xd := scaleTw x tsqdn in
  let qd := sqrtTwDnP xd in
  if [&& posFp ((tw0 x + tw1 x + tw2 x)%float), scaleOkb x tsqdn tsqup,
         wellFormed xd & finTwb qd]
  then scaleTw qd tsqhi else TWFloat nan nan nan.

(* The root of a number taken up by two to the hundred and sixty is the root  *)
(* taken up by two to the eighty, which is the whole of why this works.       *)
Lemma sqrt_tsqup v : (0 <= v)%R ->
  R_sqrt.sqrt (v * bpow radix2 160) = R_sqrt.sqrt v * bpow radix2 80.
Proof.
move=> Hv.
have -> : (160 = 2 * 80)%Z by lia.
by apply: sqrt_scale_even.
Qed.

Theorem sqrtTwUpK_ge x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwUpK x)) ->
  (R_sqrt.sqrt (twval x) <= twval (sqrtTwUpK x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwUpK.
have Hb80 := bpow_gt_0 radix2 80.
have H160 : (0 <= 160)%Z by lia.
have H80 : (0 <= 80)%Z by lia.
case Hq: (finTwb (sqrtTwUpP x)).
  by move=> _; apply: sqrtTwUpP_ge => //; apply: finTwbP.
case Hu: [&& posFp ((tw0 x + tw1 x + tw2 x)%float),
             finTwb (scaleTw x tsqup), wellFormed (scaleTw x tsqup),
             finTwb (sqrtTwUpP (scaleTw x tsqup))
           & scaleOkb (sqrtTwUpP (scaleTw x tsqup)) tsqlo tsqhi].
  move=> Fa; have /and5P[Hp Fxu Wxu Fqu Hsc] := Hu.
  have Hx0 : (0 < twval x)%R by apply: sqrtGuard_pos.
  have Exu := twval_scale_upT _ _ _ Dfin_tsqup D2R_tsqup
                H160 Fl (finTwbP _ Fxu).
  have Hge := sqrtTwUpP_ge _ (finTwbP _ Fxu) Wxu (finTwbP _ Fqu).
  have [_ Eans] := twval_scale_dnT _ _ _ _ Dfin_tsqhi D2R_tsqhi
                     H80 (finTwbP _ Fqu) Hsc.
  move: Hge; rewrite Exu (sqrt_tsqup _ (Rlt_le _ _ Hx0)) -Eans.
  by nra.
case Hdn: [&& posFp ((tw0 x + tw1 x + tw2 x)%float),
              scaleOkb x tsqdn tsqup, wellFormed (scaleTw x tsqdn)
            & finTwb (sqrtTwUpP (scaleTw x tsqdn))].
  move=> Fa; have /and4P[Hp Hsc Wxd Fqd] := Hdn.
  have Hx0 : (0 < twval x)%R by apply: sqrtGuard_pos.
  have [Fxd Exd] := twval_scale_dnT _ _ _ _ Dfin_tsqup D2R_tsqup
                      H160 Fl Hsc.
  have Hb160 := bpow_gt_0 radix2 160.
  have Hxd0 : (0 <= twval (scaleTw x tsqdn))%R by nra.
  have Hge := sqrtTwUpP_ge _ Fxd Wxd (finTwbP _ Fqd).
  have Eans := twval_scale_upT _ _ _ Dfin_tsqhi D2R_tsqhi
                 H80 (finTwbP _ Fqd) Fa.
  rewrite Eans -Exd (sqrt_tsqup _ Hxd0).
  by nra.
by move/finL_nan3.
Qed.

Theorem sqrtTwDnK_le x :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l (sqrtTwDnK x)) ->
  (twval (sqrtTwDnK x) <= R_sqrt.sqrt (twval x))%R.
Proof.
move=> Fl Ew; rewrite /sqrtTwDnK.
have Hb80 := bpow_gt_0 radix2 80.
have H160 : (0 <= 160)%Z by lia.
have H80 : (0 <= 80)%Z by lia.
case Hq: (finTwb (sqrtTwDnP x)).
  by move=> _; apply: sqrtTwDnP_le => //; apply: finTwbP.
case Hu: [&& posFp ((tw0 x + tw1 x + tw2 x)%float),
             finTwb (scaleTw x tsqup), wellFormed (scaleTw x tsqup),
             finTwb (sqrtTwDnP (scaleTw x tsqup))
           & scaleOkb (sqrtTwDnP (scaleTw x tsqup)) tsqlo tsqhi].
  move=> Fa; have /and5P[Hp Fxu Wxu Fqu Hsc] := Hu.
  have Hx0 : (0 < twval x)%R by apply: sqrtGuard_pos.
  have Exu := twval_scale_upT _ _ _ Dfin_tsqup D2R_tsqup
                H160 Fl (finTwbP _ Fxu).
  have Hle := sqrtTwDnP_le _ (finTwbP _ Fxu) Wxu (finTwbP _ Fqu).
  have [_ Eans] := twval_scale_dnT _ _ _ _ Dfin_tsqhi D2R_tsqhi
                     H80 (finTwbP _ Fqu) Hsc.
  move: Hle; rewrite Exu (sqrt_tsqup _ (Rlt_le _ _ Hx0)) -Eans.
  by nra.
case Hdn: [&& posFp ((tw0 x + tw1 x + tw2 x)%float),
              scaleOkb x tsqdn tsqup, wellFormed (scaleTw x tsqdn)
            & finTwb (sqrtTwDnP (scaleTw x tsqdn))].
  move=> Fa; have /and4P[Hp Hsc Wxd Fqd] := Hdn.
  have Hx0 : (0 < twval x)%R by apply: sqrtGuard_pos.
  have [Fxd Exd] := twval_scale_dnT _ _ _ _ Dfin_tsqup D2R_tsqup
                      H160 Fl Hsc.
  have Hb160 := bpow_gt_0 radix2 160.
  have Hxd0 : (0 <= twval (scaleTw x tsqdn))%R by nra.
  have Hle := sqrtTwDnP_le _ Fxd Wxd (finTwbP _ Fqd).
  have Eans := twval_scale_upT _ _ _ Dfin_tsqhi D2R_tsqhi
                 H80 (finTwbP _ Fqd) Fa.
  rewrite Eans -Exd (sqrt_tsqup _ Hxd0).
  by nra.
by move/finL_nan3.
Qed.

(* What it computes: the middle of the range direct, and the two ends by the  *)
(* way round -- two to the thousandth is brought down, two to the minus one   *)
(* thousand and sixtieth taken up.                                            *)
Compute (sqrtTwDnK (fp2tw 2), sqrtTwUpK (fp2tw 2)).
Compute (sqrtTwDnK (TWFloat 0x1p+1000 0 0), sqrtTwUpK (TWFloat 0x1p+1000 0 0)).
Compute (sqrtTwDnK (TWFloat 0x1p-1060 0 0), sqrtTwUpK (TWFloat 0x1p-1060 0 0)).
