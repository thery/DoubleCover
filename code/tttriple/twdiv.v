From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith Require Import twarith twbound tw_updn twpaper twflx twdivflx.
From twarith Require Import twsqrt.
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

(* AND THE SAME, IN ONE PASS.  Written as it is above, the quotient is       *)
(* worked out three times over: once inside `divOkT', once inside `div_okb'  *)
(* under it, and once again for the answer.  `threeDivG' does it once and    *)
(* hands back the flag beside it, and `threeDivGE' says the pair is the two  *)
(* computed apart -- so `divTwUpQE' below is the definition above, and every *)
(* proof goes through the equation and never sees the arrangement.           *)
Definition divTwUpQ (z x : twfloat) :=
  let: (q, ok) := threeDivG z x in
  if posFp (magDnTw x)
     && ([&& normF (tw0 z), ((tw1 z =? 0)%float || normF (tw1 z)),
             normF (tw0 x) & ((tw1 x =? 0)%float || normF (tw1 x))]
         && [&& ok, wellFormed q,
                (tw_updn.normLo <? abs (tw0 q))%float,
                finF (kscale * abs (tw0 q))%float
              & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))])
  then shiftUp q else TWFloat nan nan nan.

Definition divTwDnQ (z x : twfloat) :=
  let: (q, ok) := threeDivG z x in
  if posFp (magDnTw x)
     && ([&& normF (tw0 z), ((tw1 z =? 0)%float || normF (tw1 z)),
             normF (tw0 x) & ((tw1 x =? 0)%float || normF (tw1 x))]
         && [&& ok, wellFormed q,
                (tw_updn.normLo <? abs (tw0 q))%float,
                finF (kscale * abs (tw0 q))%float
              & finF (dw_updn.mulUpFp kscale (abs (tw0 q)))])
  then shiftDn q else TWFloat nan nan nan.

Lemma divTwUpQE z x :
  divTwUpQ z x = if posFp (magDnTw x) && divOkT z x
                 then shiftUp (threeDiv z x) else TWFloat nan nan nan.
Proof. by rewrite /divTwUpQ /divOkT threeDivGE. Qed.

Lemma divTwDnQE z x :
  divTwDnQ z x = if posFp (magDnTw x) && divOkT z x
                 then shiftDn (threeDiv z x) else TWFloat nan nan nan.
Proof. by rewrite /divTwDnQ /divOkT threeDivGE. Qed.

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
rewrite divTwUpQE; case Hp: (posFp (magDnTw y) && divOkT x y);
  last by move/finL_nan3.
by have [H _] := andb_prop _ _ Hp; move=> _; apply: divGuard_nz.
Qed.

Lemma divTwDnQ_nz x y : finL (tw2l (divTwDnQ x y)) -> twval y <> (0 : R).
Proof.
rewrite divTwDnQE; case Hp: (posFp (magDnTw y) && divOkT x y);
  last by move/finL_nan3.
by have [H _] := andb_prop _ _ Hp; move=> _; apply: divGuard_nz.
Qed.

Theorem divTwUpQ_ge x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwUpQ x y)) ->
  (twval x / twval y <= twval (divTwUpQ x y))%R.
Proof.
move=> Fx Wx Fy Wy; rewrite divTwUpQE.
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
move=> Fx Wx Fy Wy; rewrite divTwDnQE.
case Hp: (posFp (magDnTw y) && divOkT x y); last by move/finL_nan3.
have [_ Hok] := andb_prop _ _ Hp.
rewrite /shiftDn => Fw.
have [Fq Fk] := widenDn_finI _ _ Fw.
have Hw := widenDn_le _ _ Fw.
have Hk := divOkT_step _ _ Fx Wx Fy Wy Fq Hok.
by move: Hw Hk; split_Rabs; lra.
Qed.


(* ---------------------------------------------------------------------------*)
(*  When the guard fails, the two numbers are moved into the band             *)
(* ---------------------------------------------------------------------------*)

(* WHERE THE GUARD HOLDS, MEASURED.  Unlike the root's, every failure of      *)
(* `divOkT' is inside `div_okb' -- the algorithm's own products -- and none   *)
(* is in the step: at `2^-800' over one the three clauses about the answer    *)
(* are all true and `div_okb' is false.  So what has to be moved is the two   *)
(* arguments, not the answer.                                                 *)
(*                                                                            *)
(* At the top it is Dekker's splitting, which takes a word up by `2^27 + 1':   *)
(* it overflows on `z' itself above about `2^997', and on the seed `a ~ 1/x0' *)
(* when `x0' is below about `2^-997'.  At the bottom it is the products of    *)
(* the last step falling under `Dprodlo = 2^-969'.                            *)
(*                                                                            *)
(* THE QUOTIENT SCALES BY THE DIFFERENCE, not by half the sum, so there is no *)
(* evenness to respect and each argument can be moved on its own.  Six ways   *)
(* round cover every failure measured: both up, both down -- where the        *)
(* quotient does not move at all and the answer needs no correction -- and    *)
(* each of the two alone either way, where the answer is corrected by the     *)
(* same power the other way.  Two to the five hundredth is the shift: it      *)
(* takes `2^-1070' to `2^-570' and `2^1000' to `2^500', both well inside.     *)
Definition ddup := Eval compute in 0x1p+500%float.
Definition dddn := Eval compute in 0x1p-500%float.

Lemma D2R_ddup : D2R ddup = bpow radix2 500.
Proof. by rewrite /D2R /ddup; compute; lra. Qed.

Lemma Dfin_ddup : Dfin ddup.
Proof. by []. Qed.

Lemma De500 : (0 <= 500)%Z.
Proof. by lia. Qed.

(* A scaling up, and a scaling down, each with what the operation tests.      *)
Lemma scUp t : finL (tw2l t) -> finTwb (scaleTw t ddup) = true ->
  finL (tw2l (scaleTw t ddup)) /\
  (twval (scaleTw t ddup) = twval t * bpow radix2 500)%R.
Proof.
move=> Fl Ht; have Fs := finTwbP _ Ht.
by split => //; apply: (twval_scale_upT _ _ _ Dfin_ddup D2R_ddup De500).
Qed.

Lemma scDn t : finL (tw2l t) -> scaleOkb t dddn ddup = true ->
  finL (tw2l (scaleTw t dddn)) /\
  (twval (scaleTw t dddn) = twval t * bpow radix2 (-500))%R.
Proof.
move=> Fl Ht.
have [Fs Ee] := twval_scale_dnT _ _ _ _ Dfin_ddup D2R_ddup De500 Fl Ht.
split => //.
rewrite -Ee Rmult_assoc.
have -> : (bpow radix2 500 * bpow radix2 (-500) = (1 : R)).
  by rewrite -bpow_plus; have -> : (500 + -500 = 0)%Z by lia.
by rewrite Rmult_1_r.
Qed.

(* THE ONE LEMMA ALL SIX WAYS ROUND USE.  It knows nothing of how the three   *)
(* scalings were come by, only what they did to the three values: the         *)
(* quotient of the two scaled numbers is the quotient scaled by the           *)
(* difference of the two exponents, so the answer comes back by its opposite. *)
Lemma divUpQ_scale_ge z x zs xs qs ea eb :
  finL (tw2l zs) -> wellFormed zs = true ->
  finL (tw2l xs) -> wellFormed xs = true ->
  finL (tw2l (divTwUpQ zs xs)) ->
  (twval zs = twval z * bpow radix2 ea)%R ->
  (twval xs = twval x * bpow radix2 eb)%R ->
  (twval qs = twval (divTwUpQ zs xs) * bpow radix2 (eb - ea))%R ->
  (twval z / twval x <= twval qs)%R.
Proof.
move=> Fzs Wzs Fxs Wxs Fq Ez Ex Eq.
have Hge := divTwUpQ_ge _ _ Fzs Wzs Fxs Wxs Fq.
have Nxs := divTwUpQ_nz _ _ Fq.
have Ha := bpow_gt_0 radix2 ea.
have Hb := bpow_gt_0 radix2 eb.
have Nx : twval x <> (0 : R) by move: Nxs; rewrite Ex; nra.
have Hd : (bpow radix2 (eb - ea) > 0)%R by apply: bpow_gt_0.
have Hba : (bpow radix2 (eb - ea) * bpow radix2 (ea - eb) = (1 : R)).
  by rewrite -bpow_plus; have -> : (eb - ea + (ea - eb) = 0)%Z by lia.
have Ediv : (bpow radix2 (ea - eb) = bpow radix2 ea / bpow radix2 eb)%R.
  by rewrite /Rdiv -bpow_opp -bpow_plus; congr bpow; lia.
have Eqd : (twval zs / twval xs
            = twval z / twval x * bpow radix2 (ea - eb))%R.
  rewrite Ez Ex Ediv.
  by field; split; [lra | exact: Nx].
rewrite Eqd in Hge.
rewrite Eq.
apply: (Rmult_le_reg_r (bpow radix2 (ea - eb)));
  first by apply: bpow_gt_0.
have -> : (twval (divTwUpQ zs xs) * bpow radix2 (eb - ea)
           * bpow radix2 (ea - eb) = twval (divTwUpQ zs xs))%R.
  by rewrite Rmult_assoc Hba Rmult_1_r.
by [].
Qed.


Lemma divDnQ_scale_le z x zs xs qs ea eb :
  finL (tw2l zs) -> wellFormed zs = true ->
  finL (tw2l xs) -> wellFormed xs = true ->
  finL (tw2l (divTwDnQ zs xs)) ->
  (twval zs = twval z * bpow radix2 ea)%R ->
  (twval xs = twval x * bpow radix2 eb)%R ->
  (twval qs = twval (divTwDnQ zs xs) * bpow radix2 (eb - ea))%R ->
  (twval qs <= twval z / twval x)%R.
Proof.
move=> Fzs Wzs Fxs Wxs Fq Ez Ex Eq.
have Hle := divTwDnQ_le _ _ Fzs Wzs Fxs Wxs Fq.
have Nxs := divTwDnQ_nz _ _ Fq.
have Ha := bpow_gt_0 radix2 ea.
have Hb := bpow_gt_0 radix2 eb.
have Nx : twval x <> (0 : R) by move: Nxs; rewrite Ex; nra.
have Hba : (bpow radix2 (eb - ea) * bpow radix2 (ea - eb) = (1 : R)).
  by rewrite -bpow_plus; have -> : (eb - ea + (ea - eb) = 0)%Z by lia.
have Ediv : (bpow radix2 (ea - eb) = bpow radix2 ea / bpow radix2 eb)%R.
  by rewrite /Rdiv -bpow_opp -bpow_plus; congr bpow; lia.
have Eqd : (twval zs / twval xs
            = twval z / twval x * bpow radix2 (ea - eb))%R.
  rewrite Ez Ex Ediv.
  by field; split; [lra | exact: Nx].
rewrite Eqd in Hle.
rewrite Eq.
apply: (Rmult_le_reg_r (bpow radix2 (ea - eb)));
  first by apply: bpow_gt_0.
have -> : (twval (divTwDnQ zs xs) * bpow radix2 (eb - ea)
           * bpow radix2 (ea - eb) = twval (divTwDnQ zs xs))%R.
  by rewrite Rmult_assoc Hba Rmult_1_r.
by [].
Qed.

(* A NOUGHT ON TOP.  The guard asks the answer for a leading word above the  *)
(* smallest normal number, because the step it is widened by is `kscale'      *)
(* times that word; nought is not such a word, so every one of the seven     *)
(* ways below refuses a quotient of nought and hands back `nan'.  There is    *)
(* nothing there to refuse: nought over a number that is not nought is        *)
(* exactly nought, and an exact answer needs no widening.  Nor is it a        *)
(* corner.  Interval's own exponential divides by an enclosure whose lower    *)
(* end is nought, and without this line the whole enclosure comes back as     *)
(* nothing -- which is what `bench_bands.v' was reading as a refusal.         *)
Definition zeroTwb (t : twfloat) : bool :=
  [&& finTwb t, (tw0 t =? 0)%float, (tw1 t =? 0)%float & (tw2 t =? 0)%float].

Lemma D2R_zero : D2R 0%float = (0 : R).
Proof. by []. Qed.

Lemma twval_zero3 : twval (TWFloat 0%float 0%float 0%float) = (0 : R).
Proof. by rewrite /twval /= !D2R_zero; lra. Qed.

Lemma zeroTwbP t : zeroTwb t = true -> twval t = (0 : R).
Proof.
have F0 : Dfin 0%float by [].
case: t => a b c /and4P[/and3P[Fa Fb Fc] Ea Eb Ec].
rewrite /twval /= (Deqb _ _ Ea (finFP _ Fa) F0) (Deqb _ _ Eb (finFP _ Fb) F0)
        (Deqb _ _ Ec (finFP _ Fc) F0) !D2R_zero.
by lra.
Qed.

(* THE SIX WAYS ROUND.  The direct call first; then both numbers moved        *)
(* together, where the quotient does not move and the answer needs no         *)
(* correction; then each of them alone either way, where it does.  Every way  *)
(* is tested, and what is behind all seven is `nan', so the operation is      *)
(* total.                                                                     *)
Definition divTwUpK (z x : twfloat) :=
  if zeroTwb z && posFp (magDnTw x) then TWFloat 0%float 0%float 0%float else
  let q0 := divTwUpQ z x in
  if finTwb q0 then q0 else
  let zu := scaleTw z ddup in let xu := (scaleTw x ddup) in
  let zd := scaleTw z dddn in let xd := (scaleTw x dddn) in
  let a1 := divTwUpQ zu xu in
  if [&& finTwb zu, wellFormed zu, finTwb xu, wellFormed xu
       & finTwb a1] then a1 else
  let a2 := divTwUpQ zd xd in
  if [&& scaleOkb z dddn ddup, wellFormed zd, scaleOkb x dddn ddup,
         wellFormed xd & finTwb a2] then a2 else
  let a3 := divTwUpQ zu x in
  if [&& finTwb zu, wellFormed zu, finTwb a3
       & scaleOkb a3 dddn ddup]
  then scaleTw a3 dddn else
  let a4 := divTwUpQ zd x in
  if [&& scaleOkb z dddn ddup, wellFormed zd, finTwb a4
       & finTwb (scaleTw a4 ddup)]
  then scaleTw a4 ddup else
  let a5 := divTwUpQ z xu in
  if [&& finTwb xu, wellFormed xu, finTwb a5
       & finTwb (scaleTw a5 ddup)]
  then scaleTw a5 ddup else
  let a6 := divTwUpQ z xd in
  if [&& scaleOkb x dddn ddup, wellFormed xd, finTwb a6
       & scaleOkb a6 dddn ddup]
  then scaleTw a6 dddn else
  TWFloat nan nan nan.

Definition divTwDnK (z x : twfloat) :=
  if zeroTwb z && posFp (magDnTw x) then TWFloat 0%float 0%float 0%float else
  let q0 := divTwDnQ z x in
  if finTwb q0 then q0 else
  let zu := scaleTw z ddup in let xu := (scaleTw x ddup) in
  let zd := scaleTw z dddn in let xd := (scaleTw x dddn) in
  let a1 := divTwDnQ zu xu in
  if [&& finTwb zu, wellFormed zu, finTwb xu, wellFormed xu
       & finTwb a1] then a1 else
  let a2 := divTwDnQ zd xd in
  if [&& scaleOkb z dddn ddup, wellFormed zd, scaleOkb x dddn ddup,
         wellFormed xd & finTwb a2] then a2 else
  let a3 := divTwDnQ zu x in
  if [&& finTwb zu, wellFormed zu, finTwb a3
       & scaleOkb a3 dddn ddup]
  then scaleTw a3 dddn else
  let a4 := divTwDnQ zd x in
  if [&& scaleOkb z dddn ddup, wellFormed zd, finTwb a4
       & finTwb (scaleTw a4 ddup)]
  then scaleTw a4 ddup else
  let a5 := divTwDnQ z xu in
  if [&& finTwb xu, wellFormed xu, finTwb a5
       & finTwb (scaleTw a5 ddup)]
  then scaleTw a5 ddup else
  let a6 := divTwDnQ z xd in
  if [&& scaleOkb x dddn ddup, wellFormed xd, finTwb a6
       & scaleOkb a6 dddn ddup]
  then scaleTw a6 dddn else
  TWFloat nan nan nan.

(* Each way round is named, so the test and the answer are the same call.     *)
(* Written out it is two quotients a branch and up to twelve in all.          *)
Lemma divTwUpKE z x :
  divTwUpK z x =
  (if zeroTwb z && posFp (magDnTw x) then TWFloat 0%float 0%float 0%float else
   if finTwb (divTwUpQ z x) then divTwUpQ z x else
   if [&& finTwb (scaleTw z ddup), wellFormed (scaleTw z ddup),
          finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup)
        & finTwb (divTwUpQ (scaleTw z ddup) (scaleTw x ddup))]
   then divTwUpQ (scaleTw z ddup) (scaleTw x ddup) else
   if [&& scaleOkb z dddn ddup, wellFormed (scaleTw z dddn),
          scaleOkb x dddn ddup, wellFormed (scaleTw x dddn)
        & finTwb (divTwUpQ (scaleTw z dddn) (scaleTw x dddn))]
   then divTwUpQ (scaleTw z dddn) (scaleTw x dddn) else
   if [&& finTwb (scaleTw z ddup), wellFormed (scaleTw z ddup),
          finTwb (divTwUpQ (scaleTw z ddup) x)
        & scaleOkb (divTwUpQ (scaleTw z ddup) x) dddn ddup]
   then scaleTw (divTwUpQ (scaleTw z ddup) x) dddn else
   if [&& scaleOkb z dddn ddup, wellFormed (scaleTw z dddn),
          finTwb (divTwUpQ (scaleTw z dddn) x)
        & finTwb (scaleTw (divTwUpQ (scaleTw z dddn) x) ddup)]
   then scaleTw (divTwUpQ (scaleTw z dddn) x) ddup else
   if [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
          finTwb (divTwUpQ z (scaleTw x ddup))
        & finTwb (scaleTw (divTwUpQ z (scaleTw x ddup)) ddup)]
   then scaleTw (divTwUpQ z (scaleTw x ddup)) ddup else
   if [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
          finTwb (divTwUpQ z (scaleTw x dddn))
        & scaleOkb (divTwUpQ z (scaleTw x dddn)) dddn ddup]
   then scaleTw (divTwUpQ z (scaleTw x dddn)) dddn else
   TWFloat nan nan nan).
Proof. by []. Qed.

Lemma divTwDnKE z x :
  divTwDnK z x =
  (if zeroTwb z && posFp (magDnTw x) then TWFloat 0%float 0%float 0%float else
   if finTwb (divTwDnQ z x) then divTwDnQ z x else
   if [&& finTwb (scaleTw z ddup), wellFormed (scaleTw z ddup),
          finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup)
        & finTwb (divTwDnQ (scaleTw z ddup) (scaleTw x ddup))]
   then divTwDnQ (scaleTw z ddup) (scaleTw x ddup) else
   if [&& scaleOkb z dddn ddup, wellFormed (scaleTw z dddn),
          scaleOkb x dddn ddup, wellFormed (scaleTw x dddn)
        & finTwb (divTwDnQ (scaleTw z dddn) (scaleTw x dddn))]
   then divTwDnQ (scaleTw z dddn) (scaleTw x dddn) else
   if [&& finTwb (scaleTw z ddup), wellFormed (scaleTw z ddup),
          finTwb (divTwDnQ (scaleTw z ddup) x)
        & scaleOkb (divTwDnQ (scaleTw z ddup) x) dddn ddup]
   then scaleTw (divTwDnQ (scaleTw z ddup) x) dddn else
   if [&& scaleOkb z dddn ddup, wellFormed (scaleTw z dddn),
          finTwb (divTwDnQ (scaleTw z dddn) x)
        & finTwb (scaleTw (divTwDnQ (scaleTw z dddn) x) ddup)]
   then scaleTw (divTwDnQ (scaleTw z dddn) x) ddup else
   if [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
          finTwb (divTwDnQ z (scaleTw x ddup))
        & finTwb (scaleTw (divTwDnQ z (scaleTw x ddup)) ddup)]
   then scaleTw (divTwDnQ z (scaleTw x ddup)) ddup else
   if [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
          finTwb (divTwDnQ z (scaleTw x dddn))
        & scaleOkb (divTwDnQ z (scaleTw x dddn)) dddn ddup]
   then scaleTw (divTwDnQ z (scaleTw x dddn)) dddn else
   TWFloat nan nan nan).
Proof. by []. Qed.

Lemma bpow0R : bpow radix2 0 = (1 : R).
Proof. by []. Qed.

Lemma twval_id t : (twval t = twval t * bpow radix2 0)%R.
Proof. by rewrite bpow0R Rmult_1_r. Qed.

Theorem divTwUpK_ge x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwUpK x y)) ->
  (twval x / twval y <= twval (divTwUpK x y))%R.
Proof.
move=> Fx Wx Fy Wy; rewrite divTwUpKE.
case Hz: (zeroTwb x && posFp (magDnTw y)).
  move=> _; have /andP[Hz0 _] := Hz.
  by rewrite (zeroTwbP _ Hz0) twval_zero3 /Rdiv Rmult_0_l; lra.
case Hq: (finTwb (divTwUpQ x y)).
  by move=> _; apply: divTwUpQ_ge => //; apply: finTwbP.
case H1: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup)
           & finTwb (divTwUpQ (scaleTw x ddup) (scaleTw y ddup))].
  move=> _; have /and5P[Fzu Wzu Fxu Wxu Fq1] := H1.
  have [Fzu' Ezu] := scUp _ Fx Fzu.
  have [Fxu' Exu] := scUp _ Fy Fxu.
  apply: (divUpQ_scale_ge x y (scaleTw x ddup) (scaleTw y ddup) _ 500 500).
  - exact: Fzu'.
  - exact: Wzu.
  - exact: Fxu'.
  - exact: Wxu.
  - by apply: finTwbP.
  - exact: Ezu.
  - exact: Exu.
  exact: (twval_id (divTwUpQ (scaleTw x ddup) (scaleTw y ddup))).
case H2: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             scaleOkb y dddn ddup, wellFormed (scaleTw y dddn)
           & finTwb (divTwUpQ (scaleTw x dddn) (scaleTw y dddn))].
  move=> _; have /and5P[Hzd Wzd Hxd Wxd Fq2] := H2.
  have [Fzd Ezd] := scDn _ Fx Hzd.
  have [Fxd Exd] := scDn _ Fy Hxd.
  apply: (divUpQ_scale_ge x y (scaleTw x dddn) (scaleTw y dddn) _ (-500) (-500)).
  - exact: Fzd.
  - exact: Wzd.
  - exact: Fxd.
  - exact: Wxd.
  - by apply: finTwbP.
  - exact: Ezd.
  - exact: Exd.
  exact: (twval_id (divTwUpQ (scaleTw x dddn) (scaleTw y dddn))).
case H3: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (divTwUpQ (scaleTw x ddup) y)
           & scaleOkb (divTwUpQ (scaleTw x ddup) y) dddn ddup].
  move=> _; have /and4P[Fzu Wzu Fq3 Hsc] := H3.
  have [Fzu' Ezu] := scUp _ Fx Fzu.
  have [_ Eans] := scDn _ (finTwbP _ Fq3) Hsc.
  apply: (divUpQ_scale_ge x y (scaleTw x ddup) y _ 500 0).
  - exact: Fzu'.
  - exact: Wzu.
  - exact: Fy.
  - exact: Wy.
  - by apply: finTwbP.
  - exact: Ezu.
  - exact: (twval_id y).
  exact: Eans.
case H4: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             finTwb (divTwUpQ (scaleTw x dddn) y)
           & finTwb (scaleTw (divTwUpQ (scaleTw x dddn) y) ddup)].
  move=> _; have /and4P[Hzd Wzd Fq4 Fans] := H4.
  have [Fzd Ezd] := scDn _ Fx Hzd.
  have [_ Eans] := scUp _ (finTwbP _ Fq4) Fans.
  apply: (divUpQ_scale_ge x y (scaleTw x dddn) y _ (-500) 0).
  - exact: Fzd.
  - exact: Wzd.
  - exact: Fy.
  - exact: Wy.
  - by apply: finTwbP.
  - exact: Ezd.
  - exact: (twval_id y).
  exact: Eans.
case H5: [&& finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup),
             finTwb (divTwUpQ x (scaleTw y ddup))
           & finTwb (scaleTw (divTwUpQ x (scaleTw y ddup)) ddup)].
  move=> _; have /and4P[Fxu Wxu Fq5 Fans] := H5.
  have [Fxu' Exu] := scUp _ Fy Fxu.
  have [_ Eans] := scUp _ (finTwbP _ Fq5) Fans.
  apply: (divUpQ_scale_ge x y x (scaleTw y ddup) _ 0 500).
  - exact: Fx.
  - exact: Wx.
  - exact: Fxu'.
  - exact: Wxu.
  - by apply: finTwbP.
  - exact: (twval_id x).
  - exact: Exu.
  exact: Eans.
case H6: [&& scaleOkb y dddn ddup, wellFormed (scaleTw y dddn),
             finTwb (divTwUpQ x (scaleTw y dddn))
           & scaleOkb (divTwUpQ x (scaleTw y dddn)) dddn ddup].
  move=> _; have /and4P[Hxd Wxd Fq6 Hsc] := H6.
  have [Fxd Exd] := scDn _ Fy Hxd.
  have [_ Eans] := scDn _ (finTwbP _ Fq6) Hsc.
  apply: (divUpQ_scale_ge x y x (scaleTw y dddn) _ 0 (-500)).
  - exact: Fx.
  - exact: Wx.
  - exact: Fxd.
  - exact: Wxd.
  - by apply: finTwbP.
  - exact: (twval_id x).
  - exact: Exd.
  exact: Eans.
by move/finL_nan3.
Qed.

Theorem divTwDnK_le x y :
  finL (tw2l x) -> wellFormed x = true ->
  finL (tw2l y) -> wellFormed y = true ->
  finL (tw2l (divTwDnK x y)) ->
  (twval (divTwDnK x y) <= twval x / twval y)%R.
Proof.
move=> Fx Wx Fy Wy; rewrite divTwDnKE.
case Hz: (zeroTwb x && posFp (magDnTw y)).
  move=> _; have /andP[Hz0 _] := Hz.
  by rewrite (zeroTwbP _ Hz0) twval_zero3 /Rdiv Rmult_0_l; lra.
case Hq: (finTwb (divTwDnQ x y)).
  by move=> _; apply: divTwDnQ_le => //; apply: finTwbP.
case H1: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup)
           & finTwb (divTwDnQ (scaleTw x ddup) (scaleTw y ddup))].
  move=> _; have /and5P[Fzu Wzu Fxu Wxu Fq1] := H1.
  have [Fzu' Ezu] := scUp _ Fx Fzu.
  have [Fxu' Exu] := scUp _ Fy Fxu.
  apply: (divDnQ_scale_le x y (scaleTw x ddup) (scaleTw y ddup) _ 500 500).
  - exact: Fzu'.
  - exact: Wzu.
  - exact: Fxu'.
  - exact: Wxu.
  - by apply: finTwbP.
  - exact: Ezu.
  - exact: Exu.
  exact: (twval_id (divTwDnQ (scaleTw x ddup) (scaleTw y ddup))).
case H2: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             scaleOkb y dddn ddup, wellFormed (scaleTw y dddn)
           & finTwb (divTwDnQ (scaleTw x dddn) (scaleTw y dddn))].
  move=> _; have /and5P[Hzd Wzd Hxd Wxd Fq2] := H2.
  have [Fzd Ezd] := scDn _ Fx Hzd.
  have [Fxd Exd] := scDn _ Fy Hxd.
  apply: (divDnQ_scale_le x y (scaleTw x dddn) (scaleTw y dddn) _ (-500) (-500)).
  - exact: Fzd.
  - exact: Wzd.
  - exact: Fxd.
  - exact: Wxd.
  - by apply: finTwbP.
  - exact: Ezd.
  - exact: Exd.
  exact: (twval_id (divTwDnQ (scaleTw x dddn) (scaleTw y dddn))).
case H3: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (divTwDnQ (scaleTw x ddup) y)
           & scaleOkb (divTwDnQ (scaleTw x ddup) y) dddn ddup].
  move=> _; have /and4P[Fzu Wzu Fq3 Hsc] := H3.
  have [Fzu' Ezu] := scUp _ Fx Fzu.
  have [_ Eans] := scDn _ (finTwbP _ Fq3) Hsc.
  apply: (divDnQ_scale_le x y (scaleTw x ddup) y _ 500 0).
  - exact: Fzu'.
  - exact: Wzu.
  - exact: Fy.
  - exact: Wy.
  - by apply: finTwbP.
  - exact: Ezu.
  - exact: (twval_id y).
  exact: Eans.
case H4: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             finTwb (divTwDnQ (scaleTw x dddn) y)
           & finTwb (scaleTw (divTwDnQ (scaleTw x dddn) y) ddup)].
  move=> _; have /and4P[Hzd Wzd Fq4 Fans] := H4.
  have [Fzd Ezd] := scDn _ Fx Hzd.
  have [_ Eans] := scUp _ (finTwbP _ Fq4) Fans.
  apply: (divDnQ_scale_le x y (scaleTw x dddn) y _ (-500) 0).
  - exact: Fzd.
  - exact: Wzd.
  - exact: Fy.
  - exact: Wy.
  - by apply: finTwbP.
  - exact: Ezd.
  - exact: (twval_id y).
  exact: Eans.
case H5: [&& finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup),
             finTwb (divTwDnQ x (scaleTw y ddup))
           & finTwb (scaleTw (divTwDnQ x (scaleTw y ddup)) ddup)].
  move=> _; have /and4P[Fxu Wxu Fq5 Fans] := H5.
  have [Fxu' Exu] := scUp _ Fy Fxu.
  have [_ Eans] := scUp _ (finTwbP _ Fq5) Fans.
  apply: (divDnQ_scale_le x y x (scaleTw y ddup) _ 0 500).
  - exact: Fx.
  - exact: Wx.
  - exact: Fxu'.
  - exact: Wxu.
  - by apply: finTwbP.
  - exact: (twval_id x).
  - exact: Exu.
  exact: Eans.
case H6: [&& scaleOkb y dddn ddup, wellFormed (scaleTw y dddn),
             finTwb (divTwDnQ x (scaleTw y dddn))
           & scaleOkb (divTwDnQ x (scaleTw y dddn)) dddn ddup].
  move=> _; have /and4P[Hxd Wxd Fq6 Hsc] := H6.
  have [Fxd Exd] := scDn _ Fy Hxd.
  have [_ Eans] := scDn _ (finTwbP _ Fq6) Hsc.
  apply: (divDnQ_scale_le x y x (scaleTw y dddn) _ 0 (-500)).
  - exact: Fx.
  - exact: Wx.
  - exact: Fxd.
  - exact: Wxd.
  - by apply: finTwbP.
  - exact: (twval_id x).
  - exact: Exd.
  exact: Eans.
by move/finL_nan3.
Qed.

Lemma scale_nz t s e :
  (twval (scaleTw t s) = twval t * bpow radix2 e)%R ->
  twval (scaleTw t s) <> (0 : R) -> twval t <> (0 : R).
Proof.
by move=> E H; move: H; rewrite E; have := bpow_gt_0 radix2 e; nra.
Qed.

Lemma divTwUpK_nz x y :
  finL (tw2l y) -> finL (tw2l (divTwUpK x y)) -> twval y <> (0 : R).
Proof.
move=> Fy; rewrite divTwUpKE.
case Hz: (zeroTwb x && posFp (magDnTw y)).
  by move=> _; have /andP[_ Hy0] := Hz; apply: divGuard_nz.
case Hq: (finTwb (divTwUpQ x y)).
  by move=> _; apply: (divTwUpQ_nz x y); apply: finTwbP.
case H1: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup)
           & finTwb (divTwUpQ (scaleTw x ddup) (scaleTw y ddup))].
  move=> _; have /and5P[Fzu Wzu Fxu Wxu Fq] := H1.
  have [_ Exu] := scUp _ Fy Fxu.
  by apply: (scale_nz _ _ _ Exu);
     apply: (divTwUpQ_nz (scaleTw x ddup) (scaleTw y ddup)); apply: finTwbP.
case H2: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             scaleOkb y dddn ddup, wellFormed (scaleTw y dddn)
           & finTwb (divTwUpQ (scaleTw x dddn) (scaleTw y dddn))].
  move=> _; have /and5P[Hzd Wzd Hxd Wxd Fq] := H2.
  have [_ Exd] := scDn _ Fy Hxd.
  by apply: (scale_nz _ _ _ Exd);
     apply: (divTwUpQ_nz (scaleTw x dddn) (scaleTw y dddn)); apply: finTwbP.
case H3: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (divTwUpQ (scaleTw x ddup) y)
           & scaleOkb (divTwUpQ (scaleTw x ddup) y) dddn ddup].
  move=> _; have /and4P[Fzu Wzu Fq Hsc] := H3.
  by apply: (divTwUpQ_nz (scaleTw x ddup) y); apply: finTwbP.
case H4: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             finTwb (divTwUpQ (scaleTw x dddn) y)
           & finTwb (scaleTw (divTwUpQ (scaleTw x dddn) y) ddup)].
  move=> _; have /and4P[Hzd Wzd Fq Fans] := H4.
  by apply: (divTwUpQ_nz (scaleTw x dddn) y); apply: finTwbP.
case H5: [&& finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup),
             finTwb (divTwUpQ x (scaleTw y ddup))
           & finTwb (scaleTw (divTwUpQ x (scaleTw y ddup)) ddup)].
  move=> _; have /and4P[Fxu Wxu Fq Fans] := H5.
  have [_ Exu] := scUp _ Fy Fxu.
  by apply: (scale_nz _ _ _ Exu);
     apply: (divTwUpQ_nz x (scaleTw y ddup)); apply: finTwbP.
case H6: [&& scaleOkb y dddn ddup, wellFormed (scaleTw y dddn),
             finTwb (divTwUpQ x (scaleTw y dddn))
           & scaleOkb (divTwUpQ x (scaleTw y dddn)) dddn ddup].
  move=> _; have /and4P[Hxd Wxd Fq Hsc] := H6.
  have [_ Exd] := scDn _ Fy Hxd.
  by apply: (scale_nz _ _ _ Exd);
     apply: (divTwUpQ_nz x (scaleTw y dddn)); apply: finTwbP.
by move/finL_nan3.
Qed.

Lemma divTwDnK_nz x y :
  finL (tw2l y) -> finL (tw2l (divTwDnK x y)) -> twval y <> (0 : R).
Proof.
move=> Fy; rewrite divTwDnKE.
case Hz: (zeroTwb x && posFp (magDnTw y)).
  by move=> _; have /andP[_ Hy0] := Hz; apply: divGuard_nz.
case Hq: (finTwb (divTwDnQ x y)).
  by move=> _; apply: (divTwDnQ_nz x y); apply: finTwbP.
case H1: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup)
           & finTwb (divTwDnQ (scaleTw x ddup) (scaleTw y ddup))].
  move=> _; have /and5P[Fzu Wzu Fxu Wxu Fq] := H1.
  have [_ Exu] := scUp _ Fy Fxu.
  by apply: (scale_nz _ _ _ Exu);
     apply: (divTwDnQ_nz (scaleTw x ddup) (scaleTw y ddup)); apply: finTwbP.
case H2: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             scaleOkb y dddn ddup, wellFormed (scaleTw y dddn)
           & finTwb (divTwDnQ (scaleTw x dddn) (scaleTw y dddn))].
  move=> _; have /and5P[Hzd Wzd Hxd Wxd Fq] := H2.
  have [_ Exd] := scDn _ Fy Hxd.
  by apply: (scale_nz _ _ _ Exd);
     apply: (divTwDnQ_nz (scaleTw x dddn) (scaleTw y dddn)); apply: finTwbP.
case H3: [&& finTwb (scaleTw x ddup), wellFormed (scaleTw x ddup),
             finTwb (divTwDnQ (scaleTw x ddup) y)
           & scaleOkb (divTwDnQ (scaleTw x ddup) y) dddn ddup].
  move=> _; have /and4P[Fzu Wzu Fq Hsc] := H3.
  by apply: (divTwDnQ_nz (scaleTw x ddup) y); apply: finTwbP.
case H4: [&& scaleOkb x dddn ddup, wellFormed (scaleTw x dddn),
             finTwb (divTwDnQ (scaleTw x dddn) y)
           & finTwb (scaleTw (divTwDnQ (scaleTw x dddn) y) ddup)].
  move=> _; have /and4P[Hzd Wzd Fq Fans] := H4.
  by apply: (divTwDnQ_nz (scaleTw x dddn) y); apply: finTwbP.
case H5: [&& finTwb (scaleTw y ddup), wellFormed (scaleTw y ddup),
             finTwb (divTwDnQ x (scaleTw y ddup))
           & finTwb (scaleTw (divTwDnQ x (scaleTw y ddup)) ddup)].
  move=> _; have /and4P[Fxu Wxu Fq Fans] := H5.
  have [_ Exu] := scUp _ Fy Fxu.
  by apply: (scale_nz _ _ _ Exu);
     apply: (divTwDnQ_nz x (scaleTw y ddup)); apply: finTwbP.
case H6: [&& scaleOkb y dddn ddup, wellFormed (scaleTw y dddn),
             finTwb (divTwDnQ x (scaleTw y dddn))
           & scaleOkb (divTwDnQ x (scaleTw y dddn)) dddn ddup].
  move=> _; have /and4P[Hxd Wxd Fq Hsc] := H6.
  have [_ Exd] := scDn _ Fy Hxd.
  by apply: (scale_nz _ _ _ Exd);
     apply: (divTwDnQ_nz x (scaleTw y dddn)); apply: finTwbP.
by move/finL_nan3.
Qed.

(* What it computes: the middle of the range direct, and the ends by the way  *)
(* round -- a dividend too small, a divisor too small, and both too large.    *)
Compute (divTwDnK (fp2tw 1) (fp2tw 3), divTwUpK (fp2tw 1) (fp2tw 3)).
Compute (divTwDnK (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40),
         divTwUpK (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40)).
Compute (divTwDnK (fp2tw 0x1p-1070) (fp2tw 1),
         divTwUpK (fp2tw 0x1p-1070) (fp2tw 1)).
Compute (divTwDnK (fp2tw 1) (fp2tw 0x1p-1070),
         divTwUpK (fp2tw 1) (fp2tw 0x1p-1070)).
Compute (divTwDnK (fp2tw 0x1p+1000) (fp2tw 0x1p+1000),
         divTwUpK (fp2tw 0x1p+1000) (fp2tw 0x1p+1000)).
