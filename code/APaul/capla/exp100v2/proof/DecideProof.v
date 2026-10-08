(** * decide: the decision decide_Z on y and hN

    decide calls num_zero, num_copy, num_sub, num_add, num_bitlen,
    num_low, num_pow2 and num_lt: their statements are hypotheses of
    [decide_ok].  The steps are those of the VST proof (second half of
    body_maybe_hard_bits of ../../../vst/exp100/Verif_top.v): d = D,
    lo = y - D, hi = y + D; hard when lo or hi leaves the binade of y;
    f from the exponent, hard when out of [64, 184]; d = min(lo, hi) of
    lo = y mod 2^f, hi = 2^f - lo; not hard when 2^(f - 42) + D < d. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** The number D = 16 *)

(* The limbs of a row of zeros. *)
Lemma pval_zero_row k : (k <= NL)%nat ->
  pval ([ffun=> Int64.zero] : numA) k = 0%Z.
Proof.
elim: k => [|k IH] Hk; first by rewrite pval0.
by rewrite (pvalSn _ _ Hk) ffunE (IH (ltnW Hk)) Int64.unsigned_zero Z.mul_0_r.
Qed.

(* One limb written in a row of zeros. *)
Lemma valA_write1 k x (H : (k < NL)%nat) :
  valA (([ffun=> Int64.zero] : numA) ↑[k ← x]) =
  (limb_base k * Int64.unsigned x)%Z.
Proof.
rewrite -pval_all (pval_setf _ _ _ H _ (leqnn _)) H pval_zero_row // ffunE.
rewrite Int64.unsigned_zero; ring.
Qed.

(* One limb written in a row of zeros: an array of limbs. *)
Lemma limbsA_write1 k x (H : (k < NL)%nat) : limb (Int64.unsigned x) ->
  limbsA (([ffun=> Int64.zero] : numA) ↑[k ← x]).
Proof. by move=> Hx i; rewrite (setfP _ _ _ H) ffunE; case: eqP. Qed.

(** ** Words of the exponent computation *)

(* A signed word of a value: the value modulo 2^64. *)
Lemma eqm_signed_repr x : Int64.eqm (Int64.signed (Int64.repr x)) x.
Proof.
apply: Int64.eqm_trans; first exact: Int64.eqm_signed_unsigned.
exact/Int64.eqm_sym/Int64.eqm_unsigned_repr.
Qed.

Lemma sub_repr x y :
  Int64.sub (Int64.repr x) (Int64.repr y) = Int64.repr (x - y).
Proof.
rewrite Int64.sub_signed; apply: Int64.eqm_samerepr.
by apply: Int64.eqm_sub; apply: eqm_signed_repr.
Qed.

Lemma add_repr x y :
  Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof.
rewrite Int64.add_signed; apply: Int64.eqm_samerepr.
by apply: Int64.eqm_add; apply: eqm_signed_repr.
Qed.

(* The bound of the small values of decide. *)
Definition small64 (x : Z) : Prop := (- 2 ^ 62 <= x <= 2 ^ 62)%Z.

Lemma signed_small x : small64 x -> Int64.signed (Int64.repr x) = x.
Proof.
rewrite /small64 => H; apply: Int64.signed_repr.
change Int64.min_signed with (-9223372036854775808)%Z.
change Int64.max_signed with 9223372036854775807%Z.
have E : (2 ^ 62 = 4611686018427387904)%Z by [].
lia.
Qed.

Lemma small64_le x : (- 10000 <= x <= 10000)%Z -> small64 x.
Proof.
rewrite /small64 => H; have E : (2 ^ 62 = 4611686018427387904)%Z by [].
lia.
Qed.

(* e = hN - 160 + b - 1 *)
Lemma e_word hN b :
  Int64.sub (Int64.add (Int64.sub hN (Int64.repr 160)) (Int64.repr b))
    (Int64.repr 1) = Int64.repr (Int64.signed hN - 160 + b - 1).
Proof.
by rewrite -{1}(Int64.repr_signed hN) sub_repr add_repr sub_repr.
Qed.

(* fs = ve - 53 - (hN - 160) *)
Lemma fs_word V hN :
  Int64.sub (Int64.sub (Int64.repr V) (Int64.repr 53))
    (Int64.sub hN (Int64.repr 160)) =
  Int64.repr (V - 53 - (Int64.signed hN - 160)).
Proof.
by rewrite -{1}(Int64.repr_signed hN) sub_repr sub_repr sub_repr.
Qed.

Lemma lt_small x y : small64 x -> small64 y ->
  Int64.lt (Int64.repr x) (Int64.repr y) = (x <? y)%Z.
Proof.
move=> Hx Hy; rewrite /Int64.lt (signed_small x Hx) (signed_small y Hy).
case: Coqlib.zlt => H; symmetry; [apply/Z.ltb_lt | apply/Z.ltb_ge]; lia.
Qed.

(* A small value read back as unsigned. *)
Lemma unsigned_small x : (0 <= x <= 192)%Z ->
  Int64.unsigned (Int64.repr x) = x.
Proof.
move=> H; apply: Int64.unsigned_repr.
change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* Two bit lengths are equal as words exactly when they are equal. *)
Lemma eq_bits x y : (0 <= x <= 192)%Z -> (0 <= y <= 192)%Z ->
  Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y)%Z.
Proof.
move=> Hx Hy; rewrite /Int64.eq (unsigned_small x Hx) (unsigned_small y Hy).
case: Coqlib.zeq => H; symmetry; [apply/Z.eqb_eq | apply/Z.eqb_neq]; lia.
Qed.

(* The constant -1022 as Capla writes it. *)
Lemma repr_m1022 : Int64.repr 18446744073709550594 = Int64.repr (-1022).
Proof. by apply: Int64.eqm_samerepr; exists 1%Z. Qed.

(** ** The numbers of decide, in Z *)

(* The bit length of a number of six limbs. *)
Lemma bitlen192 v : (0 <= v < 2 ^ 192)%Z ->
  (0 <= ExpModel.bitlen v <= 192)%Z.
Proof. exact: ExpModelBounds.bitlen_bound. Qed.

(* A number of six limbs is below 2^192. *)
Lemma valA192 (a : numA) : limbsA a -> (0 <= valA a < 2 ^ 192)%Z.
Proof. by move/valA_bound; rewrite /limb_base /limb_bits. Qed.

(* lo = y mod 2^f is below 2^f. *)
Lemma low_lt y f : (0 <= f)%Z ->
  (0 <= ExpModel.low y f < ExpModel.pow2 f)%Z.
Proof.
move=> Hf; rewrite ExpModel.lowE // ExpModel.pow2E //.
apply: Z.mod_pos_bound; lia.
Qed.

(* 2^(f - m_hard) + D fits in six limbs. *)
Lemma pow2_add_D k : (0 <= k <= 142)%Z -> (ExpModel.pow2 k + 16 < 2 ^ 192)%Z.
Proof.
move=> Hk; rewrite (ExpModel.pow2E k (proj1 Hk)).
have := Z.pow_le_mono_r 2 k 142 ltac:(lia) ltac:(lia).
have : (2 ^ 142 + 16 < 2 ^ 192)%Z by apply/Z.ltb_lt.
generalize (2 ^ k)%Z (2 ^ 142)%Z (2 ^ 192)%Z; lia.
Qed.

(* The decision once the binade is known and f is in its range. *)
Lemma decide_end y s f :
  ExpModel.bitlen (y - 16) = ExpModel.bitlen y ->
  ExpModel.bitlen (y + 16) = ExpModel.bitlen y ->
  f = (Z.max (s - 160 + ExpModel.bitlen y - 1) (-1022) - 53 - (s - 160))%Z ->
  (64 <= f <= 184)%Z ->
  ExpModel.decide_Z y s =
  (if ExpModel.pow2 (f - 42) + 16 <?
      (if ExpModel.low y f <? ExpModel.pow2 f - ExpModel.low y f
       then ExpModel.low y f else ExpModel.pow2 f - ExpModel.low y f)
   then 0 else 1)%Z.
Proof.
move=> H1 H2 Hf Rf.
rewrite (ExpModelBounds.decide_f y s f H1 H2 Hf).
have Ef : ((f <? ExpModel.f_min) || (ExpModel.f_max <? f))%Z = false.
{ have -> : ExpModel.f_max = 184%Z by [].
  rewrite /ExpModel.f_min.
  by apply/negbTE/negP => /orP [] /Z.ltb_lt; lia. }
by rewrite Ef.
Qed.

(* f out of its range: hard. *)
Lemma decide_out y s f :
  ExpModel.bitlen (y - 16) = ExpModel.bitlen y ->
  ExpModel.bitlen (y + 16) = ExpModel.bitlen y ->
  f = (Z.max (s - 160 + ExpModel.bitlen y - 1) (-1022) - 53 - (s - 160))%Z ->
  (f < 64 \/ 184 < f)%Z ->
  ExpModel.decide_Z y s = 1%Z.
Proof.
move=> H1 H2 Hf Rf.
rewrite (ExpModelBounds.decide_f y s f H1 H2 Hf).
have Ef : ((f <? ExpModel.f_min) || (ExpModel.f_max <? f))%Z = true.
{ have -> : ExpModel.f_max = 184%Z by [].
  rewrite /ExpModel.f_min.
  by case: Rf => H; apply/orP; [left | right]; apply/Z.ltb_lt. }
by rewrite Ef.
Qed.

(** ** The proof *)

Theorem decide_ok :
  num_add_spec -> num_bitlen_spec -> num_copy_spec -> num_low_spec ->
  num_lt_spec -> num_pow2_spec -> num_sub_spec -> num_zero_spec ->
  decide_spec.
Proof.
move=> NA NB NC NLo NLt NP2 NS NZ μ y hN lo hi d t r rl Ly Ry RhN.
have Vy := valA192 _ Ly.
have H16 : (16 <= valA y)%Z.
{ have : (16 <= 2 ^ ExpConsts.P)%Z by apply/Z.leb_le. lia. }
have Hy16 : (valA y + 16 < 2 ^ ExpModel.num_bits)%Z.
{ have : (2 ^ ExpModelBounds.y_bits + 16 <= 2 ^ ExpModel.num_bits)%Z.
    by apply/Z.leb_le.
  lia. }
have Rs : (- 4096 <= Int64.signed hN <= 4096)%Z.
{ by move: RhN; have -> : (2 ^ ExpModelBounds.hN_bits = 4096)%Z by []. }
start; csteps.
(* d = D, lo = y - D, hi = y + D *)
call NZ => ->.
csteps.
call NC => ->.
csteps.
call NS.
rewrite -!setfE.
set D := (([ffun=> Int64.zero] : numA) ↑[_ ← _]).
have LD : limbsA D by apply: limbsA_write1.
have VD : valA D = 16 by rewrite valA_write1.
move=> /(_ Ly LD ltac:(lia)) [lo1 [-> [Llo1 Vlo1]]].
rewrite VD in Vlo1.
csteps.
call NC => ->.
csteps.
call NA => /(_ Ly LD ltac:(lia)) [hi1 [-> [Lhi1 Vhi1]]].
rewrite VD in Vhi1.
csteps.
(* the bit lengths of y, lo, hi *)
call NB => /(_ Ly) [-> ->].
csteps.
call NB => /(_ Llo1) [-> ->].
csteps.
call NB => /(_ Lhi1) [-> ->].
csteps.
have Rb := bitlen192 _ Vy.
have Rbl := bitlen192 _ (valA192 _ Llo1).
have Rbh := bitlen192 _ (valA192 _ Lhi1).
(* y - D or y + D out of the binade of y: hard *)
rewrite (eq_bits _ _ Rbl Rb).
case B1: (ExpModel.bitlen (valA lo1) =? ExpModel.bitlen (valA y))%Z => /=.
2: { csteps; fin.
     split; last by do 4 eexists.
     rewrite ExpModelBounds.decide_bits //; left.
     change (ExpModel.bitlen (valA y - 16) <> ExpModel.bitlen (valA y)).
     rewrite -Vlo1; exact/Z.eqb_neq. }
csteps.
rewrite (eq_bits _ _ Rbh Rb).
case B2: (ExpModel.bitlen (valA hi1) =? ExpModel.bitlen (valA y))%Z => /=.
2: { csteps; fin.
     split; last by do 4 eexists.
     rewrite ExpModelBounds.decide_bits //; right.
     change (ExpModel.bitlen (valA y + 16) <> ExpModel.bitlen (valA y)).
     rewrite -Vhi1; exact/Z.eqb_neq. }
move/Z.eqb_eq: B1; rewrite Vlo1 => B1.
move/Z.eqb_eq: B2; rewrite Vhi1 => B2.
csteps.
(* f = max(e, emin) - 53 - (hN - 160), e = hN - 160 + b - 1 *)
set bb := ExpModel.bitlen (valA y) in B1 B2 Rb *.
have [F HF] : exists F, F = (Z.max (Int64.signed hN - 160 + bb - 1) (-1022)
                             - 53 - (Int64.signed hN - 160))%Z by eexists.
have RF : (- 10000 <= F <= 10000)%Z by rewrite HF; lia.
rewrite (e_word hN bb) repr_m1022 lt_small; try (apply: small64_le; lia).
case C1: (-1022 <? Int64.signed hN - 160 + bb - 1)%Z => /=.
all: csteps.
1: have EF : (Int64.signed hN - 160 + bb - 1 - 53 - (Int64.signed hN - 160)
              = F)%Z by rewrite HF; move/Z.ltb_lt: C1; lia.
2: have EF : (-1022 - 53 - (Int64.signed hN - 160) = F)%Z
     by rewrite HF; move/Z.ltb_ge: C1; lia.
all: rewrite fs_word EF.
(* f out of [64, 184]: hard *)
all: rewrite lt_small; try (apply: small64_le; lia).
all: case C2: (F <? 64)%Z => /=.
1,3: csteps; fin; split; last (by do 4 eexists);
     rewrite (decide_out (valA y) (Int64.signed hN) F B1 B2 HF) //;
     by left; exact/Z.ltb_lt.
all: csteps.
all: clear C1 EF.
all: rewrite lt_small; try (apply: small64_le; lia).
all: case C3: (184 <? F)%Z => /=.
1,3: csteps; fin; split; last (by do 4 eexists);
     rewrite (decide_out (valA y) (Int64.signed hN) F B1 B2 HF) //;
     by right; exact/Z.ltb_lt.
all: move/Z.ltb_ge: C2 => C2; move/Z.ltb_ge: C3 => C3.
all: csteps.
(* lo = y mod 2^f, hi = 2^f - lo *)
all: have HFu : Int64.unsigned (Int64.repr F) = F by apply: unsigned_small; lia.
all: have HF192 : (Int64.unsigned (Int64.repr F) < ExpModel.num_bits)%Z
       by rewrite HFu; have -> : ExpModel.num_bits = 192%Z by []; lia.
all: call NLo => /(_ Ly HF192) [lo2 [-> [Llo2 Vlo2]]].
all: rewrite HFu in Vlo2.
all: csteps.
all: call NP2 => /(_ HF192) [hi2 [-> [Lhi2 Vhi2]]].
all: rewrite HFu in Vhi2.
all: have HL := low_lt (valA y) F ltac:(lia).
all: csteps.
all: call NS => /(_ Lhi2 Llo2 ltac:(rewrite Vlo2 Vhi2; lia))
                [hi3 [-> [Lhi3 Vhi3]]].
all: rewrite Vhi2 Vlo2 in Vhi3.
all: csteps.
all: call NLt => /(_ Llo2 Lhi3) [-> ->].
all: rewrite Vlo2 Vhi3.
all: csteps.
(* d = min(lo, hi): the two branches go on apart *)
all: case C4: (ExpModel.low (valA y) F <?
               ExpModel.pow2 F - ExpModel.low (valA y) F)%Z => /=.
all: csteps.
all: call NC => ->.
all: csteps.
(* t = 2^(f - m_hard) + D *)
all: have U42 :
       Int64.unsigned (Int64.sub (Int64.repr F) (Int64.repr 42)) = (F - 42)%Z
       by rewrite sub_repr; apply: unsigned_small; lia.
all: have H42 : (Int64.unsigned (Int64.sub (Int64.repr F) (Int64.repr 42)) <
                 ExpModel.num_bits)%Z
       by rewrite U42; have -> : ExpModel.num_bits = 192%Z by []; lia.
all: call NP2 => /(_ H42) [t1 [-> [Lt1 Vt1]]].
all: rewrite U42 in Vt1.
all: csteps.
all: call NZ => ->.
all: csteps.
all: call NA.
all: rewrite -!setfE -/D.
all: move=> /(_ Lt1 LD ltac:(rewrite Vt1 VD; apply: pow2_add_D; lia))
              [t2 [-> [Lt2 Vt2]]].
all: rewrite Vt1 VD in Vt2.
all: csteps.
(* the test t < d *)
all: call NLt => /(_ Lt2 ltac:(first [exact Llo2 | exact Lhi3])) [-> ->].
all: csteps.
all: have Ed := decide_end (valA y) (Int64.signed hN) F B1 B2 HF ltac:(lia).
all: rewrite C4 -?Vhi3 -?Vlo2 -Vt2 in Ed.
all: case C5: (valA t2 <? _)%Z => /=.
all: csteps; fin; split; last (by do 4 eexists).
all: by rewrite Ed C5.
Qed.
