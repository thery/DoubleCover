(** * num_sub: the spec (task T3) *)

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
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* One step of the loop, on the numbers: the new limb w and borrow c'. *)
Lemma num_sub_step xs xs' ys nk (c w : int64) (c' : Z) :
  (nk < 6)%coq_nat -> length xs = 6%nat -> length ys = 6%nat ->
  length xs' = 6%nat ->
  List.nth nk xs' Int64.zero = List.nth nk xs Int64.zero ->
  (Int64.unsigned w - c' * 2 ^ 32 =
   Int64.unsigned (List.nth nk xs Int64.zero) -
   Int64.unsigned (List.nth nk ys Int64.zero) - Int64.unsigned c)%Z ->
  (val32 (firstn nk xs') - Int64.unsigned c * base32 nk =
   val32 (firstn nk xs) - val32 (firstn nk ys))%Z ->
  (val32 (firstn (S nk) (replace nk xs' w)) - c' * base32 (S nk) =
   val32 (firstn (S nk) xs) - val32 (firstn (S nk) ys))%Z.
Proof.
  move=> Hk Hx Hy Hl Ha Ew HV.
  rewrite !val32_firstn_S ?replace_length ?Hl ?Hx ?Hy //.
  rewrite firstn_replace nth_replace_same ?Hl // base32S.
  move: HV Ew; set a := Int64.unsigned (List.nth nk xs _);
    set b := Int64.unsigned (List.nth nk ys _).
  move=> HV Ew.
  have -> : (Int64.unsigned w = a - b - Int64.unsigned c + c' * 2 ^ 32)%Z by lia.
  lia.
Qed.

(* a = a - b, for a >= b *)
Theorem num_sub_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs xs -> limbs ys ->
  (val32 ys <= val32 xs)%Z ->
  eval_funcall ge (Internal num_sub27)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  exists xs', e1!(param 0 num_sub27) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\ val32 xs' = (val32 xs - val32 ys)%Z.
Proof.
  move=> Hx Hy Lx Ly Hs.
  intro_eval_funcall num_sub27 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "a" A.
  name_var "b" B.
  name_var "c" CY.
  repeat prog.
  (* after k steps: the low k limbs of a hold a - b modulo 2^(32 k), borrow c *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k xs' c,
      e!i = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      let nk := nat_of k in
      e!A = Some (Varr (map Vint64 xs')) /\
      e!CY = Some (Vint64 c) /\
      (Int64.unsigned c <= 1)%Z /\
      length xs' = 6%nat /\
      (forall p, (nk <= p)%coq_nat ->
         List.nth p xs' Int64.zero = List.nth p xs Int64.zero) /\
      (forall p, (p < nk)%coq_nat ->
         (Int64.unsigned (List.nth p xs' Int64.zero) < 2 ^ 32)%Z) /\
      (val32 (firstn nk xs') - Int64.unsigned c * base32 nk =
       val32 (firstn nk xs) - val32 (firstn nk ys))%Z.
  exists Inv; split.
  - exists (Int64.repr 0), xs, (Int64.repr 0).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xs' & c & [= ->] & Hk6 & [= ->] & [= ->] & Hc & Hl & Hout & Hlo & HV)
      => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      change (Z.to_nat (Int64.unsigned k)) with nk.
      rewrite !nth_map_V64 ?length_map; try lia.
      have Ha : List.nth nk xs' Int64.zero = List.nth nk xs Int64.zero
        by apply: Hout; lia.
      rewrite Ha.
      wsimpl.
      set a := List.nth nk xs Int64.zero.
      set b := List.nth nk ys Int64.zero.
      have La : (Int64.unsigned a < 2 ^ 32)%Z by apply: Lx.
      have Lb : (Int64.unsigned b < 2 ^ 32)%Z by apply: Ly.
      have Et : Int64.unsigned (Int64.add b c) =
                (Int64.unsigned b + Int64.unsigned c)%Z.
      { have := Int64.unsigned_range b; have := Int64.unsigned_range c.
        clia b, c. }
      case LT: (Int64.ltu a (Int64.add b c)); simplWP; repeat prog;
        simplWP; repeat prog.
      all: change (Z.to_nat (Int64.unsigned k)) with nk;
        rewrite !nth_map_V64 ?length_map; try lia; rewrite Ha; wsimpl.
      * (* a < b + c: borrow *)
        have Hlt : (Int64.unsigned a < Int64.unsigned b + Int64.unsigned c)%Z.
        { move: LT; rewrite /Int64.ltu Et; case: zlt => //. }
        set w := Int64.sub (Int64.add a (Int64.repr 4294967296)) (Int64.add b c).
        have Ew : Int64.unsigned w =
          (Int64.unsigned a + 2 ^ 32 - (Int64.unsigned b + Int64.unsigned c))%Z.
        { rewrite /w -Et; have := Int64.unsigned_range a.
          have := Int64.unsigned_range (Int64.add b c).
          move: La Lb Hc Et Hlt; clia a, b, c. }
        exists (Int64.add k (Int64.repr 1)), (replace nk xs' w), (Int64.repr 1).
        rewrite Hk1 replace_map; repeat split => //.
        all: first [ clia k | by rewrite replace_length | idtac ].
        -- move=> p Hp; rewrite nth_replace_other; try lia; apply: Hout; lia.
        -- move=> p Hp.
           have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
           ++ rewrite nth_replace_other; try lia; apply: Hlo; lia.
           ++ rewrite nth_replace_same ?Hl // Ew; lia.
        -- apply: (num_sub_step xs xs' ys nk c w) => //.
           change (Int64.unsigned (Int64.repr 1)) with 1%Z; lia.
      * (* a >= b + c: no borrow *)
        have Hge : (Int64.unsigned b + Int64.unsigned c <= Int64.unsigned a)%Z.
        { move: LT; rewrite /Int64.ltu Et; case: zlt => // H _; lia. }
        set w := Int64.sub a (Int64.add b c).
        have Ew : Int64.unsigned w =
          (Int64.unsigned a - (Int64.unsigned b + Int64.unsigned c))%Z.
        { rewrite /w -Et; have := Int64.unsigned_range a.
          have := Int64.unsigned_range (Int64.add b c).
          move: Et Hge; clia a, b, c. }
        exists (Int64.add k (Int64.repr 1)), (replace nk xs' w), (Int64.repr 0).
        rewrite Hk1 replace_map; repeat split => //.
        all: first [ clia k | by rewrite replace_length | idtac ].
        -- move=> p Hp; rewrite nth_replace_other; try lia; apply: Hout; lia.
        -- move=> p Hp.
           have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
           ++ rewrite nth_replace_other; try lia; apply: Hlo; lia.
           ++ rewrite nth_replace_same ?Hl // Ew; lia.
        -- apply: (num_sub_step xs xs' ys nk c w) => //.
           change (Int64.unsigned (Int64.repr 0)) with 0%Z; lia.
    + (* the loop ends with k = 6: the borrow is 0 *)
      have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      have F6 : forall l : list int64, length l = 6%nat -> firstn 6 l = l.
      { by move=> l Hl6; apply: List.firstn_all2; rewrite Hl6. }
      move: HV; rewrite -/nk Ek (F6 xs') // (F6 xs) // (F6 ys) // => HV.
      repeat prog.
      have Lx' : limbs xs'.
      { move=> p; have [Hp|Hp] : (p < 6)%coq_nat \/ (6 <= p)%coq_nat by lia.
        - apply: Hlo; rewrite -/nk Ek; lia.
        - rewrite nth_overflow ?Hl //; rewrite Int64.unsigned_zero; lia. }
      have Hb := val32_bound xs' Lx'; rewrite Hl in Hb.
      have Hc0 : Int64.unsigned c = 0%Z.
      { have := Int64.unsigned_range c; have := base32_pos 6;
        have := val32_nonneg xs'; nia. }
      exists xs'; repeat split => //.
      move: HV; rewrite Hc0; lia.
Qed.
