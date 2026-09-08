(* Copyright (c) ENS de Lyon and Inria. All rights reserved. *)
From  Drincq Require Import MoreFlocq Remarks.
Require Import ROmega.
Require Import Psatz.
Require Import Flocq.Calc.Fcalc_digits.
Require Import Flocq.Prop.Fprop_div_sqrt_error.
Require Import Flocq.Calc.Fcalc_ops.
Require Import Flocq.Calc.Fcalc_bracket.
Require Import Flocq.Calc.Fcalc_round.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Prop.Fprop_plus_error.
Require Import Flocq.Prop.Fprop_Sterbenz.
Require Import mathcomp.ssreflect.ssreflect.
From Double Require Import Bayleyaux.
From Double Require Import F2Sum.

Set Implicit Arguments.

(* Definition two := radix2. Let two := radix2. Local Notation two := radix2. *)
Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).
Local Open Scope Z_scope.

Section TwoSum.
Variables p  : Z.
(* Hypothesis Hp : Zlt 1 p. *)
Hypothesis Hp4: Zle 4 p.

Local Fact  p_gt_1 : (Z.lt 1  p).
now apply Zlt_le_trans with (2 := Hp4).
Qed.
Local Instance   p_gt_0 : Prec_gt_0 p.
now apply Zlt_le_trans with (2 := Hp4).
Qed.

Local Notation fexp := (FLX_exp p).

Local Notation format := (generic_format two fexp).
Local Notation cexp := (canonic_exp two fexp).
Local Notation mant := (scaled_mantissa two fexp).


Variable choice : Z -> bool.
Hypothesis ZNE : choice = (fun n => negb (Zeven n)).

(* 
Variables a b s a' b' da db t : R.
Hypothesis Fa : format a.
Hypothesis Fb : format b.
Hypothesis sDef : s = rnd_p (a + b).
Hypothesis a'Def : a' = rnd_p (s - b).
Hypothesis b'Def : b' = rnd_p (s - a').
Hypothesis daDef : da = rnd_p (a - a').
Hypothesis dbDef : db = rnd_p (b - b').
Hypothesis tDef : t = rnd_p (da + db).*)

Local Notation rnd_p := (round two fexp (Znearest choice )).

Theorem TwoSum (a b s a' b' da db t : R) 
(Fa : format a) (Fb : format b) 
(sDef : s = rnd_p (a + b)) 
(a'Def : a' = rnd_p (s - b))
(b'Def : b' = rnd_p (s - a'))
(daDef : da = rnd_p (a - a'))
(dbDef : db = rnd_p (b - b'))
(tDef : t = rnd_p (da + db)) : (t = a + b - s)%R.
Proof.
case :(Req_dec a 0)=> a0.
  move: sDef; rewrite a0 Rplus_0_l round_generic  // => sb.
  move:  a'Def b'Def daDef dbDef tDef; rewrite sb a0.
  rewrite Rminus_diag_eq // round_0 => ->.
  rewrite !Rminus_0_r  round_generic  // round_0 => -> ->.
  rewrite Rminus_diag_eq // round_0 => ->.
  by rewrite Rplus_0_l round_0.
wlog apos : a b s a' b' da db t Fa Fb sDef a'Def b'Def daDef dbDef tDef a0 /  (0 < a)%R.
 move => hlog.
 case: ( R0_lt_dec  a0).
  apply: hlog=>//.
  by rewrite -a'Def -daDef -b'Def -dbDef.
 move => aneg.
 suff : (-t = - a + -b  -  (-s))%R by lra.
 have hopp r1 r2: (-r1 = -r2)%R -> (r1 = r2)%R by lra.
 have hmo r1 r2: (r1 - -r2)%R = (r2 + r1)%R by ring.
 by apply : (hlog (-a)%R  (-b)%R (Ropp s) (Ropp a') (Ropp b')  
     (Ropp da)( Ropp db)(Ropp t)); 
     try lra; try  apply: generic_format_opp =>//; apply: hopp;
     rewrite ZNE -round_NE_opp Ropp_minus_distr hmo !Ropp_involutive -ZNE.
case:(Rle_or_lt (Rabs a) (Rabs b)) => absab.
 rewrite Rplus_comm in sDef |- *.
 have: (format (s-b)%R).
  case:(@Fast2Sum _ p_gt_1 choice b a Fb Fa )=>//.
   by apply:canonic_exp_monotone_abs.
rewrite -sDef.

  move=>  <- _ .
   apply:generic_format_round.
 intro smb_float.
 assert (a' = s - b)%R as smb_exact.
  by rewrite a'Def; apply: round_generic.
 rewrite tDef.
 have -> :(db  = 0%R).
  rewrite dbDef.
  move: b'Def; rewrite smb_exact.
  replace (s - (s - b))%R with b by lra.
  by rewrite round_generic // => ->; rewrite Rminus_diag_eq    ?round_0.
 rewrite Rplus_0_r daDef smb_exact round_generic; last by apply: generic_format_round.
 rewrite round_generic; first by ring.
 replace (a - (s - b))%R with (-(s - (b + a)))%R by ring.
 by apply:generic_format_opp;  rewrite sDef;  apply: plus_error.
move/Rabs_lt_inv: absab.
rewrite Rabs_pos_eq; last by lra.
move=>[hmab hba].
(* cas Sterbenz *)
case (Rle_lt_dec  b (-a/2)%R)=> hab.
 have sab: s = (a + b)%R.
  rewrite sDef round_generic //.
  replace (a + b)%R with (a - -b)%R by lra.
  by apply:(sterbenz two fexp  a (-b)%R) =>//;try lra ;  apply:generic_format_opp.
 move: a'Def b'Def daDef dbDef.
 rewrite sab tDef.
 replace (a + b - b)%R with a by ring.
 rewrite round_generic // => ->.
 replace (a + b - a)%R with b by ring.
 rewrite round_generic // => ->.
 by rewrite !Rminus_diag_eq // round_0=> -> ->; rewrite Rplus_0_r round_0.
(* -a/2 < b < a *)
have habs: ((Rabs b) <= (Rabs s))%R.
 case (Rle_lt_dec 0  b %R)=> hb0.
  have h2b: ((b*2) <= (a + b))%R by lra.
  have {h2b} h2b: (rnd_p (b * 2) <= s)%R.
   by rewrite sDef; apply:round_le.
  rewrite !Rabs_pos_eq; try lra.
   have h2: (2 = pow 1)%R by rewrite bpow_1.
   by move:h2b; rewrite h2 round_bpow -h2 round_generic //; lra.
  have <-: (rnd_p 0 = 0)%R by rewrite round_0.
  by rewrite sDef; apply:round_le; lra.
 have h2: (-(a + b) <= b)%R by lra.
 have : (- s <= b)%R.
  rewrite sDef.
  have {2}-> : b = rnd_p b.
   by rewrite round_generic.
  have -> : (- rnd_p (a + b) = rnd_p (- (a + b)))%R.
   by rewrite ZNE round_NE_opp.
  by apply: round_le.
 have: (b <= s)%R.
  rewrite sDef.
  have {1}->: (b = rnd_p b) by rewrite round_generic.
  by apply: round_le; lra.
 move=> hbs hsb.
 rewrite (Rabs_pos_eq s); first by apply:Rabs_le.
(* move before *)
 have <-: (rnd_p 0 = 0)%R by rewrite round_0.
 by rewrite sDef; apply:round_le; lra.
case :(Req_dec b 0)=> b0.
 move: sDef; rewrite b0 Rplus_0_r  round_generic  // => sb.
 move:  a'Def b'Def daDef dbDef tDef; rewrite sb b0.
 rewrite !Rminus_0_r  round_generic // => ->; rewrite   Rminus_diag_eq // round_0 => -> -> .
 by rewrite Rminus_0_r Rplus_0_l round_0=> ->; rewrite round_0.
case:(@Fast2Sum _ p_gt_1 choice s (Ropp b))=>//.
- by rewrite sDef; apply: generic_format_round.
- by apply:generic_format_opp.
- rewrite canonic_exp_opp.
  by apply: canonic_exp_monotone_abs.
move=> h1 h2.
have hdb: db = (a' -(s -b))%R.
 rewrite dbDef.
 have -> : ((b - b') = - (b' -b))%R by ring.
 rewrite ZNE round_NE_opp.
 have -> : (a' - (s - b) = - ((s-b) - a'))%R by ring.
 apply/Ropp_eq_compat.
 move: h1 h2.
 have -> : ((s + - b)= s - b)%R by [].
 rewrite -a'Def.

 have -> : ((a' - s)= - (s - a'))%R by ring.
 rewrite ZNE round_NE_opp.
 move/Ropp_eq_compat; rewrite /Rminus !Ropp_involutive b'Def ZNE=> ->.
 by have ->: (- b + (s + - a'))%R = (s + - a' + - b)%R by ring.
suff hda: da = (a - a')%R.
 rewrite tDef hdb hda.
 have -> : (a - a' + (a' - (s - b)))%R = (a + b - s)%R by ring.
 rewrite round_generic //.
 have -> : (a + b - s)%R = (- (s - (a + b)))%R by ring.
 by apply: generic_format_opp; rewrite sDef; apply:plus_error.
(* need p >= 4 *)
case:(rnd_epsl p_gt_1 choice (a +b)%R)=> eps1 [heps1 hs].
case:(rnd_epsl p_gt_1 choice (s -b)%R)=> eps2 [heps2 ha'].
have h2a': (a' = (a + a*eps1 + b*eps1)*(1 + eps2))%R.
 by rewrite a'Def ha' sDef hs; ring.
have hvba: (-a < b <a)%R by lra.
pose x := ((a + b)/(2*a))%R.
have hx0: (0 < x )%R.
 rewrite /x;  try lra.
 apply:(Rmult_lt_reg_l  (2 * a)%R); try lra.
 by field_simplify; lra.
have hx1: (x < 1)%R.
 rewrite /x.
 apply:(Rmult_lt_reg_r  (2 * a)%R); try lra.
 by field_simplify; lra.
pose eps3 := (x * eps1)%R.
have : (Rabs eps3 <=  pow (- p))%R.
 rewrite /eps3.
 apply: Rabs_le.
 move/Rabs_le_inv : heps2 =>  [heps2 heps22].
 move/Rabs_le_inv : heps1 =>  [heps1 heps11].
 case:(Rlt_le_dec 0 eps1)=> h01.
  split; try lra.
   apply:(Rle_trans _ R0); try lra.
   apply: Rlt_le. 
   clear - hx0 h01.
   by apply: Rmult_lt_0_compat.
  rewrite -(Rmult_1_l  (pow (- p))).
  by apply:Rmult_le_compat; lra.
 split; last first.
  apply:(Rle_trans _ R0); try lra.
  rewrite -(Rmult_0_r x).
  by apply:Rmult_le_compat_l; lra.
 apply:(Rle_trans _ eps1); try lra.
 rewrite Rmult_comm -{1}(Rmult_1_r eps1).
 by apply: Rmult_le_compat_neg_l; lra.
move=> heps3.
rewrite daDef.
apply: round_generic.
apply: sterbenz' =>//.
 by rewrite a'Def; apply: generic_format_round.
have h3: (a * eps1 + b * eps1 = (2 * a)* eps3)%R.
 rewrite /eps3 /x.
 by field_simplify.
move: h2a'; rewrite Rplus_assoc h3.
have -> :  ((a + 2 * a * eps3) * (1 + eps2))%R = (a * (2 * eps3* eps2 + 2* eps3 + eps2 +1))%R.
 by ring_simplify.
set eta := (2 * eps3 * eps2 + 2 * eps3 + eps2)%R.
have: ((Rabs eta) <= (3 * (pow (-p)) + 2 * (pow (-p))^2))%R.
 rewrite /eta.
 apply:(Rle_trans _ (Rabs (2 * eps3 * eps2 + 2 * eps3) + Rabs eps2)%R).
  by apply:Rabs_triang.
 have h4: (Rabs (2 * eps3 * eps2 + 2 * eps3) + Rabs eps2 <=
      (Rabs (2 * eps3 * eps2) + Rabs (2 * eps3) + Rabs eps2))%R.
  apply:Rplus_le_compat_r.
  by apply:Rabs_triang.
 apply:(Rle_trans _  (Rabs (2 * eps3 * eps2) + Rabs (2 * eps3) + Rabs eps2)%R)=>//.
 rewrite 2!Rabs_mult.
 rewrite (Rabs_pos_eq 2%R); try lra.
 have -> : (pow (- p) ^ 2 = pow (- p) * pow (- p))%R by field.
 have hpowp := (bpow_ge_0 two (-p)).
 apply: (Rle_trans _ (2 * Rabs eps3 * Rabs eps2 + 2 * Rabs eps3 +  pow (- p))%R); try lra.
 apply: (Rle_trans _ (2 * Rabs eps3 * Rabs eps2 + 2 * pow (-p) +  pow (- p))%R).
  by lra.
 apply: (Rle_trans _ (2 * (pow(-p)) * (pow(-p)) + 2 * pow (-p) +  pow (- p))%R).
  have h5: (Rabs eps3 * Rabs eps2  <= pow (- p) * pow (- p))%R.
   have hh1:= Rabs_pos eps1.
   have hh2:= Rabs_pos eps2.
   have hh3:= Rabs_pos eps3.
   by apply: Rmult_le_compat; lra.
  have: (2 * Rabs eps3 * Rabs eps2  <= 2 * pow (- p) * pow (- p))%R.
   rewrite !Rmult_assoc.
   apply: Rmult_le_compat; try lra.
   have hh1:= Rabs_pos eps1.
   have hh2:= Rabs_pos eps2.
   have hh3:= Rabs_pos eps3.
   by apply: Rmult_le_pos; lra.
  by lra.
 by lra.
move=> habseta a'e.
suff /Rabs_lt_inv  [h4 h5]: ((Rabs eta) < 1/2)%R.
 split; try lra.
  rewrite a'e.
  have h6 : (1/2 < eta +1)%R by lra.
  by apply:(Rmult_le_compat_l a); try  lra.
 rewrite a'e Rmult_comm.
 by apply:(Rmult_le_compat_r a); lra.
apply: (Rle_lt_trans _ (3 * pow (- p) + 2 * pow (- p) ^ 2)%R)=>//.
suff h : (pow (-p) < 1/8)%R.
 apply: (Rlt_trans _ (3/8 + 1/4*1/8)%R).
  have h4:= (bpow_gt_0 two (-p)).
  apply :(Rlt_trans _ (3/8 + 2 * pow (- p) ^ 2)%R); try lra.
  apply :(Rlt_le_trans _ (3/8 + 2 * (1/8) ^ 2)%R).
   have h5:  (pow (- p) ^ 2 <  (1 / 8)*(1/8))%R.
    have -> : (pow (- p) ^ 2 = (pow (- p) * (pow (- p))))%R by ring_simplify.
    move:(Rlt_le _  _ h4)=> {h4} h4.
    by  apply: Rmult_lt_compat.
   by apply:(Rlt_le_trans _ ((3 / 8 + 2 * (1/8)*(1/8))));lra.
  by field_simplify; lra.
 by lra.
have hp3: 3 < p by lia.
have hp4:= (bpow_lt  two 3 p hp3).
rewrite bpow_opp /Rdiv Rmult_1_l.
apply:Rinv_lt; try lra.
by rewrite bpow_powerRZ /= in hp4; lra.
Qed.

Lemma TwoSum_correct a b (Fa: format a ) (Fb: format b):
let s := rnd_p (a + b) in 
let a' := rnd_p (s - b) in 
let  b' := rnd_p (s - a') in 
let da := rnd_p (a - a') in 
let db := rnd_p (b - b') in
let t := rnd_p (da + db) in (t = a + b - s)%R.
Proof.
move=> s a' b' da db t.
apply: TwoSum =>//.
Qed.
End TwoSum.









