(** * num_bitlen, num_scale: the specs (task T6) *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
Require Import Exp100Capla.GroupALemmas.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla.NumBasicProof.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* the number of bits of a *)
Theorem num_bitlen_spec xs e1 result :
  length xs = 6%nat -> limbs xs ->
  eval_funcall ge (Internal num_bitlen70) [Varr (map Vint64 xs)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.bitlen (val32 xs))).
Proof.
  move=> Hx Lx.
  intro_eval_funcall num_bitlen70 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  apply_WP_stmt exec out e1 se1.
  name_var "i" I.
  name_var "k" K.
  name_var "b" BL.
  repeat prog.
  (* after i limbs: b is the bit length of the low i limbs *)
  pose Inv := fun (e: env) (se: senv) =>
    exists i b,
      e!I = Some (Vint64 i) /\ (Int64.unsigned i <= 6)%Z /\
      e!BL = Some (Vint64 b) /\
      Int64.unsigned b = ExpModel.bitlen (val32 (firstn (nat_of i) xs)).
  exists Inv; split.
  - exists (Int64.repr 0), (Int64.repr 0).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (i & b & [= ->] & Hi6 & [= ->] & Hb) => /=.
    tidy.
    set ni := nat_of i.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hi : (ni < 6)%coq_nat by rewrite /ni /nat_of; clia i.
      have Hi1 : nat_of (Int64.add i (Int64.repr 1)) = S ni.
      { rewrite /ni /nat_of; clia i. }
      set X := val32 (firstn ni xs).
      set w := Int64.unsigned (List.nth ni xs Int64.zero).
      (* after k bits of limb i: b is the bit length of X + 2^(32 i) (a_i mod 2^k) *)
      pose Inv2 := fun (e: env) (se: senv) =>
        exists kk b',
          e!K = Some (Vint64 kk) /\ (Int64.unsigned kk <= 32)%Z /\
          e!BL = Some (Vint64 b') /\
          Int64.unsigned b' =
            ExpModel.bitlen (X + base32 ni * (w mod 2 ^ Int64.unsigned kk)).
      exists Inv2; split.
      * exists (Int64.repr 0), b.
        change (Int64.unsigned (Int64.repr 0)) with 0%Z.
        rewrite Z.pow_0_r Z.mod_1_r Z.mul_0_r Z.add_0_r.
        repeat split => //.
      * move=>>.
        repeat prog.
        rewrite/Inv2 /=.
        intros (kk & b' & [= ->] & Hk32 & [= ->] & Hb') => /=.
        simplWP.
        case END2: Int64.ltu; simplWP.
        -- repeat prog.
           have Hk : (Int64.unsigned kk < 32)%Z.
           { by move: END2; rewrite /Int64.ltu; case: zlt. }
           have Hk1 : Int64.unsigned (Int64.add kk (Int64.repr 1)) =
                      (Int64.unsigned kk + 1)%Z by clia kk.
           change (Z.to_nat (Int64.unsigned i)) with ni.
           rewrite !nth_map_V64 ?length_map; try lia.
           wsimpl.
           rewrite bit_amt; first lia.
           rewrite -/w.
           have HX : (0 <= X < base32 ni)%Z.
           { split; first exact: val32_nonneg.
             have := val32_bound _ (limbs_firstn xs ni Lx).
             by rewrite length_firstn (_ : Init.Nat.min ni (length xs) = ni) //; lia. }
           have Hstep := bitlen_step X ni w (Int64.unsigned kk)
                           (proj1 (Int64.unsigned_range kk)) HX.
           have Hv := Z.mod_pos_bound (w / 2 ^ Int64.unsigned kk) 2 ltac:(lia).
           case EB: (Int64.eq (Int64.repr ((w / 2 ^ Int64.unsigned kk) mod 2))
                              (Int64.repr 1)); simplWP; repeat prog;
             simplWP; repeat prog.
           ++ (* bit k is 1 *)
              have Ev : ((w / 2 ^ Int64.unsigned kk) mod 2 = 1)%Z.
              { move: EB; rewrite /Int64.eq.
                rewrite Int64.unsigned_repr; first by change Int64.max_unsigned with
                  18446744073709551615%Z; lia.
                by case: zeq. }
              wsimpl.
              have Hi32 : (Int64.unsigned i < 6)%Z by move: Hi; rewrite /ni /nat_of; lia.
              set bw := Int64.add (Int64.add (Int64.mul (Int64.repr 32) i) kk)
                          (Int64.repr 1).
              have Eb : Int64.unsigned bw =
                        (32 * Int64.unsigned i + Int64.unsigned kk + 1)%Z.
              { rewrite /bw; move: Hi32 Hk; clia i, kk. }
              exists (Int64.add kk (Int64.repr 1)), bw; rewrite Hk1.
              repeat split => //; first lia.
              rewrite Hstep Ev /= Eb /ni /nat_of Z2Nat.id //.
              exact: (proj1 (Int64.unsigned_range i)).
           ++ (* bit k is 0 *)
              have Ev : ((w / 2 ^ Int64.unsigned kk) mod 2 = 0)%Z.
              { move: EB; rewrite /Int64.eq.
                rewrite Int64.unsigned_repr; first by change Int64.max_unsigned with
                  18446744073709551615%Z; lia.
                case: zeq => // H _; move: H.
                change (Int64.unsigned (Int64.repr 1)) with 1%Z; lia. }
              exists (Int64.add kk (Int64.repr 1)), b'; rewrite Hk1.
              repeat split => //; first lia.
              by rewrite Hstep Ev Z.eqb_refl.
        -- (* the 32 bits of limb i are scanned *)
           have Ek : Int64.unsigned kk = 32%Z.
           { move: END2 Hk32; rewrite /Int64.ltu; case: zlt => // H _; move: H.
             change (Int64.unsigned (Int64.repr 32)) with 32%Z; lia. }
           repeat prog.
           exists (Int64.add i (Int64.repr 1)), b'; rewrite Hi1.
           repeat split => //; first clia i.
           rewrite Hb' Ek val32_firstn_S ?Hx // -/X -/w.
           rewrite (Z.mod_small w) // /w; split.
           ++ exact: (proj1 (Int64.unsigned_range _)).
           ++ exact: Lx.
    + (* the 6 limbs are scanned *)
      have Ei : ni = 6%nat by move: END Hi6; rewrite /ni /nat_of; clia i.
      repeat prog.
      move=> ->; congr Vint64.
      rewrite -[b]Int64.repr_unsigned Hb -/ni Ei List.firstn_all2 // Hx //.
Qed.

(* a = floor(v 2^e), for v < 2^53 and e < 128 *)
Theorem num_scale_spec xs v e e1 result :
  length xs = 6%nat -> (Int64.unsigned v < 2 ^ mant53)%Z ->
  (Int64.signed e < scale_emax)%Z ->
  eval_funcall ge (Internal num_scale92)
    [Varr (map Vint64 xs); Vint64 v; Vint64 e] e1 (Some result) ->
  exists xs', e1!(param 0 num_scale92) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.scale (Int64.unsigned v) (Int64.signed e).
Proof.
  move=> Hx Hv He.
  intro_eval_funcall num_scale92 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "a" A.
  repeat prog.
  move=> _ _ CALL.
  have E1 := num_zero_spec _ _ _ Hx CALL.
  change (param 0 num_zero6) with A in E1.
  repeat prog.
  rewrite E1; simplWP; repeat prog.
  tidy; clear CALL.
  wsimpl.
  case LT: (Int64.lt e (Int64.repr 0)); simplWP; repeat prog.
  - (* e < 0: w = v >> -e in limbs 0 and 1 *)
    case LT2: (Int64.lt (Int64.repr 18446744073709551552) e); simplWP; repeat prog;
      simplWP; repeat prog; wsimpl.
    all: have HE0 : (Int64.signed e < 0)%Z by
      move: LT; rewrite /Int64.lt; case: zlt => //;
      change (Int64.signed (Int64.repr 0)) with 0%Z.
    all: have Hv53 : (0 <= Int64.unsigned v < 2 ^ 53)%Z by
      move: Hv; rewrite /mant53; have := Int64.unsigned_range v; lia.
    all: change (Z.to_nat (Int64.unsigned (Int64.repr 1))) with (addn 0 1);
      change (Z.to_nat (Int64.unsigned (Int64.repr 0))) with 0%nat.
    all: rewrite (_ : [Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero;
                  Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero] =
                 map Vint64 (repeat Int64.zero 6)) //.
    all: rewrite !replace_map.
    all: match goal with |- context [Int64.and ?W (Int64.repr 4294967295)] =>
      set w := W end.
    all: have [Hl2 [Hv2 Hlim2]] := val32_write2 0 (Int64.and w (Int64.repr 4294967295))
           (Int64.shru' w (Int.modu (Int.repr 32) Int64.iwordsize')) ltac:(lia).
    all: rewrite ExpModel.scaleE.
    all: case: (Z.leb_spec 0 (Int64.signed e)) => [|_]; first lia.
    + (* -64 < e < 0 *)
      have HE1 : (-64 < Int64.signed e)%Z.
      { move: LT2; rewrite /Int64.lt; case: zlt => //; try (move=> H _; move: H;
        change (Int64.signed (Int64.repr 18446744073709551552)) with (-64)%Z; lia). }
      have Hn := unsigned_neg e HE0.
      have Ew : Int64.unsigned w =
                (Int64.unsigned v / 2 ^ (- Int64.signed e))%Z.
      { rewrite /w shr_amt; first lia. by rewrite Hn. }
      have Hw : (0 <= Int64.unsigned w < 2 ^ 53)%Z.
      { rewrite Ew; split; first (apply: Z.div_pos; try apply: Z.pow_pos_nonneg; lia).
        apply: (Z.le_lt_trans _ (Int64.unsigned v)); last lia.
        apply: Z.div_le_upper_bound; first (apply: Z.pow_pos_nonneg; lia).
        have : (1 <= 2 ^ (- Int64.signed e))%Z.
        { have := Z.pow_pos_nonneg 2 (- Int64.signed e); lia. }
        nia. }
      eexists; split; first reflexivity.
      split; first exact: Hl2.
      split.
      * apply: Hlim2.
        -- rewrite and_mask; have := Z.mod_pos_bound (Int64.unsigned w) (2 ^ 32)
             ltac:(lia); lia.
        -- rewrite shru32; apply: Z.div_lt_upper_bound; lia.
      * by rewrite Hv2 base32_0 Z.mul_1_l split_word.
    + (* e <= -64: 0 *)
      have HE1 : (Int64.signed e <= -64)%Z.
      { move: LT2; rewrite /Int64.lt; case: zlt => //; try (move=> H _; move: H;
        change (Int64.signed (Int64.repr 18446744073709551552)) with (-64)%Z; lia). }
      eexists; split; first reflexivity.
      split; first exact: Hl2.
      split.
      * by apply: Hlim2; rewrite /w; [rewrite and_mask | rewrite shru32].
      * rewrite Hv2 base32_0 Z.mul_1_l split_word /w.
        rewrite Z.div_small //; split; first lia.
        apply: (Z.lt_le_trans _ (2 ^ 53)); first lia.
        apply: Z.pow_le_mono_r; lia.
  - (* e >= 0: v 2^b written at limbs q, q + 1, q + 2 *)
    wsimpl.
    have HE0 : (0 <= Int64.signed e)%Z.
    { move: LT; rewrite /Int64.lt; case: zlt => // H _; move: H.
      change (Int64.signed (Int64.repr 0)) with 0%Z; lia. }
    have Hue := unsigned_signed_nonneg e HE0.
    set E := Int64.signed e in HE0 He Hue *.
    have HE : (0 <= E < 128)%Z by move: He; rewrite /scale_emax; lia.
    have Hr := Z.mod_pos_bound E 32 ltac:(lia).
    have Hqb : (0 <= E / 32 < 4)%Z.
    { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }

    set q := Z.to_nat (E / 32).
    have Eq0 : Z.to_nat (Int64.unsigned (Int64.divu e (Int64.repr 32))) = q.
    { by rewrite divu32 Hue. }
    have Eq1 : Z.to_nat (Int64.unsigned (Int64.add (Int64.divu e (Int64.repr 32))
                 (Int64.repr 1))) = (q + 1)%coq_nat.
    { have := divu32 e; rewrite Hue => Hd.
      have : (Int64.unsigned (Int64.add (Int64.divu e (Int64.repr 32))
                (Int64.repr 1)) = E / 32 + 1)%Z.
      { move: Hd Hqb; set d := Int64.divu e (Int64.repr 32); clia d. }
      rewrite /q; lia. }
    have Eq2 : Z.to_nat (Int64.unsigned (Int64.add (Int64.divu e (Int64.repr 32))
                 (Int64.repr 2))) = (q + 2)%coq_nat.
    { have := divu32 e; rewrite Hue => Hd.
      have : (Int64.unsigned (Int64.add (Int64.divu e (Int64.repr 32))
                (Int64.repr 2)) = E / 32 + 2)%Z.
      { move: Hd Hqb; set d := Int64.divu e (Int64.repr 32); clia d. }
      rewrite /q; lia. }
    rewrite Eq0 Eq1 Eq2.
    rewrite (_ : [Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero;
                  Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero] =
                 map Vint64 (repeat Int64.zero 6)) //.
    rewrite !replace_map.
    set lo := Int64.shl' (Int64.and v (Int64.repr 4294967295)) _.
    set hi := Int64.add _ _.
    have Hm : (Int64.unsigned (Int64.modu e (Int64.repr 32)) < 64)%Z.
    { rewrite modu32; lia. }
    have Hv53 : (0 <= Int64.unsigned v < 2 ^ 53)%Z.
    { move: Hv; rewrite /mant53; have := Int64.unsigned_range v; lia. }
    have Hvl := Z.mod_pos_bound (Int64.unsigned v) (2 ^ 32) ltac:(lia).
    have Hp : (0 < 2 ^ (E mod 32) <= 2 ^ 31)%Z.
    { split; first by apply: Z.pow_pos_nonneg; lia.
      apply: Z.pow_le_mono_r; lia. }
    have Elo : Int64.unsigned lo =
               (Int64.unsigned v mod 2 ^ 32 * 2 ^ (E mod 32))%Z.
    { rewrite /lo shl_amt // and_mask modu32 Hue Z.mod_small //; nia. }
    have Hvh : (0 <= Int64.unsigned v / 2 ^ 32 < 2 ^ 21)%Z.
    { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }
    have Ehi : Int64.unsigned hi =
               (Int64.unsigned v / 2 ^ 32 * 2 ^ (E mod 32) +
                Int64.unsigned lo / 2 ^ 32)%Z.
    { have Hh0 : Int64.unsigned (Int64.shl' (Int64.shru' v
                   (Int.modu (Int.repr 32) Int64.iwordsize'))
                   (Int.modu (Int64.loword (Int64.modu e (Int64.repr 32)))
                      Int64.iwordsize')) =
                 (Int64.unsigned v / 2 ^ 32 * 2 ^ (E mod 32))%Z.
      { rewrite shl_amt // shru32 modu32 Hue Z.mod_small //; nia. }
      have Hl0 := shru32 lo.
      have Hlo1 : (0 <= Int64.unsigned lo / 2 ^ 32 < 2 ^ 31)%Z.
      { rewrite Elo; split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound];
          nia. }
      have HA : (0 <= Int64.unsigned v / 2 ^ 32 * 2 ^ (E mod 32) < 2 ^ 52)%Z.
      { have -> : (2 ^ 52 = 2 ^ 21 * 2 ^ 31)%Z by []. nia. }
      rewrite /hi Int64.add_unsigned Hh0 Hl0.
      rewrite Int64.unsigned_repr //.
      change Int64.max_unsigned with 18446744073709551615%Z; lia. }
    have Hhi : (0 <= Int64.unsigned hi < 2 ^ 53)%Z.
    { rewrite Ehi.
      have HA : (0 <= Int64.unsigned v / 2 ^ 32 * 2 ^ (E mod 32) < 2 ^ 52)%Z.
      { have -> : (2 ^ 52 = 2 ^ 21 * 2 ^ 31)%Z by []. nia. }
      have Hlo1 : (0 <= Int64.unsigned lo / 2 ^ 32 < 2 ^ 31)%Z.
      { rewrite Elo; split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound];
          nia. }
      lia. }
    have Hq2 : (q + 2 < 6)%coq_nat by rewrite /q; lia.
    have [Hl3 [Hv3 Hlim3]] := val32_write3 q
      (Int64.and lo (Int64.repr 4294967295))
      (Int64.and hi (Int64.repr 4294967295))
      (Int64.shru' hi (Int.modu (Int.repr 32) Int64.iwordsize')) Hq2.
    have Hx0 := and_mask lo; have Hx1 := and_mask hi; have Hx2 := shru32 hi.
    eexists; split; first reflexivity.
    split; first exact: Hl3.
    split.
    + apply: Hlim3.
      * rewrite Hx0; have := Z.mod_pos_bound (Int64.unsigned lo) (2 ^ 32)
          ltac:(lia); lia.
      * rewrite Hx1; have := Z.mod_pos_bound (Int64.unsigned hi) (2 ^ 32)
          ltac:(lia); lia.
      * rewrite Hx2; apply: Z.div_lt_upper_bound; lia.
    + rewrite Hv3 Hx0 Hx1 Hx2.
      rewrite (scale_pos (Int64.unsigned v) E (Int64.unsigned lo)
                 (Int64.unsigned hi) Hv53 HE Elo Ehi).
      rewrite ExpModel.scaleE.
      by case: (Z.leb_spec 0 E) => //; lia.
Qed.
