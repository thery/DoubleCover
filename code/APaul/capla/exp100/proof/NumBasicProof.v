(** * num_zero, num_copy, num_pow2, num_low: the specs (task T2) *)

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

(* Six zero words: the number 0. *)
Lemma zeros6 : length (repeat Int64.zero 6) = 6%nat /\
  limbs (repeat Int64.zero 6) /\ val32 (repeat Int64.zero 6) = 0%Z.
Proof.
  split => //; split; last by rewrite /= Int64.unsigned_zero.
  move=> p; case: (Nat.lt_ge_cases p 6) => Hp.
  - by rewrite nth_repeat_lt // Int64.unsigned_zero.
  - by rewrite nth_overflow ?repeat_length // Int64.unsigned_zero.
Qed.

(* a = 0 *)
Theorem num_zero_spec xs e1 result :
  length xs = 6%nat ->
  eval_funcall ge (Internal num_zero6) [Varr (map Vint64 xs)] e1 (Some result) ->
  e1!(param 0 num_zero6) = Some (Varr (map Vint64 (repeat Int64.zero 6))).
Proof.
  move=> Hx.
  intro_eval_funcall num_zero6 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "a" A.
  repeat prog.
  (* the first k limbs are 0 *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k xs',
      e!i = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      e!A = Some (Varr (map Vint64 xs')) /\ length xs' = 6%nat /\
      (forall p, (p < nat_of k)%coq_nat ->
         List.nth p xs' Int64.zero = Int64.zero).
  exists Inv; split.
  - exists (Int64.repr 0), xs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xs' & [= ->] & Hk6 & [= ->] & Hl & Hlo) => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      change (Z.to_nat (Int64.unsigned k)) with nk.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      exists (Int64.add k (Int64.repr 1)), (replace nk xs' Int64.zero).
      rewrite Hk1 replace_map; repeat split => //.
      * clia k.
      * by rewrite replace_length.
      * move=> p Hp.
        have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
        -- rewrite nth_replace_other; try lia; apply: Hlo; lia.
        -- rewrite nth_replace_same ?Hl //.
    + have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      repeat prog.
      have -> // : xs' = repeat Int64.zero 6.
      apply: list6_ext => // p Hp.
      rewrite nth_repeat_lt //; apply: Hlo; rewrite -/nk Ek //.
Qed.

(* a = b *)
Theorem num_copy_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat ->
  eval_funcall ge (Internal num_copy12)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  e1!(param 0 num_copy12) = Some (Varr (map Vint64 ys)).
Proof.
  move=> Hx Hy.
  intro_eval_funcall num_copy12 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "a" A.
  name_var "b" B.
  repeat prog.
  (* the first k limbs are those of b *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k xs',
      e!i = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      e!A = Some (Varr (map Vint64 xs')) /\ length xs' = 6%nat /\
      (forall p, (p < nat_of k)%coq_nat ->
         List.nth p xs' Int64.zero = List.nth p ys Int64.zero).
  exists Inv; split.
  - exists (Int64.repr 0), xs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xs' & [= ->] & Hk6 & [= ->] & Hl & Hlo) => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      change (Z.to_nat (Int64.unsigned k)) with nk.
      rewrite !nth_map_V64 ?length_map; try lia.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      exists (Int64.add k (Int64.repr 1)),
        (replace nk xs' (List.nth nk ys Int64.zero)).
      rewrite Hk1 replace_map; repeat split => //.
      * clia k.
      * by rewrite replace_length.
      * move=> p Hp.
        have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
        -- rewrite nth_replace_other; try lia; apply: Hlo; lia.
        -- rewrite nth_replace_same ?Hl //.
    + have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      repeat prog.
      have -> // : xs' = ys.
      apply: list6_ext => // p Hp.
      apply: Hlo; rewrite -/nk Ek //.
Qed.

(* a = 2^f, for f < 192 *)
Theorem num_pow2_spec xs f e1 result :
  length xs = 6%nat -> (Int64.unsigned f < ExpModel.num_bits)%Z ->
  eval_funcall ge (Internal num_pow272) [Varr (map Vint64 xs); Vint64 f]
    e1 (Some result) ->
  exists xs', e1!(param 0 num_pow272) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.pow2 (Int64.unsigned f).
Proof.
  move=> Hx Hf.
  intro_eval_funcall num_pow272 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "a" A.
  repeat prog.
  move=> _ _ CALL.
  have E1 := num_zero_spec _ _ _ Hx CALL.
  change (param 0 num_zero6) with A in E1.
  repeat prog.
  rewrite E1; simplWP; repeat prog.
  tidy; clear CALL.
  rewrite /sem_binarith /sem_cast /shrink /=.
  rewrite /divu64 /modu64 /= eq32 /= /shl64 /Ops.sem_cast /=.
  move=> _ _; rewrite index1 divu32.
  repeat prog.
  have Hf' : (0 <= Int64.unsigned f < 192)%Z.
  { have := Int64.unsigned_range f; move: Hf; rewrite /ExpModel.num_bits.
    change (limb_bits * Z.of_nat NL)%Z with 192%Z; lia. }
  set w := Int64.shl' _ _.
  have Hw : Int64.unsigned w = (2 ^ (Int64.unsigned f mod 32))%Z.
  { have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
    rewrite /w shl_amt modu32; first lia.
    change (Int64.unsigned (Int64.repr 1)) with 1%Z.
    rewrite Z.mul_1_l Z.mod_small //; split; first lia.
    apply: Z.pow_lt_mono_r; lia. }
  have [Hl [Hlim Hv]] := pow2_limbs _ _ Hf' Hw.
  exists (replace (Z.to_nat (Int64.unsigned f / 32)) (repeat Int64.zero 6) w).
  rewrite (_ : [Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero;
                Vint64 Int64.zero; Vint64 Int64.zero; Vint64 Int64.zero] =
               map Vint64 (repeat Int64.zero 6)) // replace_map.
  repeat split => //.
  rewrite Hv ExpModel.pow2E //; lia.
Qed.

(* a = b mod 2^f, for f < 192 *)
Theorem num_low_spec xs ys f e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs ys ->
  (Int64.unsigned f < ExpModel.num_bits)%Z ->
  eval_funcall ge (Internal num_low81)
    [Varr (map Vint64 xs); Varr (map Vint64 ys); Vint64 f] e1 (Some result) ->
  exists xs', e1!(param 0 num_low81) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.low (val32 ys) (Int64.unsigned f).
Proof.
  move=> Hx Hy Ly Hf.
  have Hf' : (0 <= Int64.unsigned f < 192)%Z.
  { have := Int64.unsigned_range f; move: Hf; rewrite /ExpModel.num_bits.
    change (limb_bits * Z.of_nat NL)%Z with 192%Z; lia. }
  have Hd : (0 <= Int64.unsigned f / 32 < 6)%Z.
  { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }
  pose j := Z.to_nat (Int64.unsigned f / 32).
  have Hj : (j < 6)%coq_nat by rewrite /j; lia.
  intro_eval_funcall num_low81 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "a" A.
  name_var "b" B.
  repeat prog.
  pose w := Int64.and (List.nth j ys Int64.zero)
    (Int64.sub (Int64.shl' (Int64.repr 1)
       (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
       (Int64.repr 1)).
  (* limb p of b mod 2^f *)
  pose tgt p := if (p <? j)%nat then List.nth p ys Int64.zero
                else if (p =? j)%nat then w else Int64.zero.
  (* the first k limbs are those of b mod 2^f *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k xs',
      e!i = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      e!A = Some (Varr (map Vint64 xs')) /\ length xs' = 6%nat /\
      (forall p, (p < nat_of k)%coq_nat -> List.nth p xs' Int64.zero = tgt p).
  exists Inv; split.
  - exists (Int64.repr 0), xs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xs' & [= ->] & Hk6 & [= ->] & Hl & Hlo) => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      wsimpl.
      case T1: (Int64.ltu k (Int64.divu f (Int64.repr 32))); simplWP; repeat prog;
        simplWP; repeat prog.
      * (* below limb f / 32: a copy *)
        have Hkj : (nk < j)%coq_nat.
        { move: T1; rewrite /Int64.ltu divu32 /nk /j /nat_of; case: zlt => //; lia. }
        change (Z.to_nat (Int64.unsigned k)) with nk.
        rewrite !nth_map_V64 ?length_map; try lia.
        exists (Int64.add k (Int64.repr 1)),
          (replace nk xs' (List.nth nk ys Int64.zero)).
        rewrite Hk1 replace_map; repeat split => //.
        -- clia k.
        -- by rewrite replace_length.
        -- move=> p Hp.
           have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
           ++ rewrite nth_replace_other; try lia; apply: Hlo; lia.
           ++ rewrite nth_replace_same ?Hl // /tgt.
              by case: (Nat.ltb_spec nk j) => //; lia.
      * wsimpl.
        case T2: (Int64.eq k (Int64.divu f (Int64.repr 32))); simplWP; repeat prog;
          simplWP; repeat prog.
        -- (* limb f / 32: the low bits *)
           have Hkj : nk = j.
           { move: T2; rewrite /Int64.eq divu32 /nk /j /nat_of; case: zeq => //.
             move=> -> _; lia. }
           change (Z.to_nat (Int64.unsigned k)) with nk.
           rewrite !nth_map_V64 ?length_map; try lia.
           wsimpl.
           exists (Int64.add k (Int64.repr 1)), (replace nk xs' w).
           rewrite Hk1 replace_map; repeat split => //.
           all: first [ clia k | by rewrite replace_length | by rewrite /w Hkj
                      | idtac ].
           move=> p Hp.
           have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
           ++ rewrite nth_replace_other; try lia; apply: Hlo; lia.
           ++ rewrite nth_replace_same ?Hl // /tgt Hkj.
              by case: (Nat.ltb_spec j j); [lia | rewrite Nat.eqb_refl].
        -- (* above limb f / 32: zero *)
           have Hkj : (j < nk)%coq_nat.
           { move: T1 T2; rewrite /Int64.ltu /Int64.eq divu32 /nk /j /nat_of.
             case: zlt => // H1 _; case: zeq => // H2 _; lia. }
           change (Z.to_nat (Int64.unsigned k)) with nk.
           exists (Int64.add k (Int64.repr 1)), (replace nk xs' Int64.zero).
           rewrite Hk1 replace_map; repeat split => //.
           ++ clia k.
           ++ by rewrite replace_length.
           ++ move=> p Hp.
              have [Hp'|->] : (p < nk)%coq_nat \/ p = nk by lia.
              ** rewrite nth_replace_other; try lia; apply: Hlo; lia.
              ** rewrite nth_replace_same ?Hl // /tgt.
                 case: (Nat.ltb_spec nk j); first lia.
                 by case: (Nat.eqb_spec nk j); first lia.
    + have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      repeat prog.
      have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
      have Hw : Int64.unsigned w =
                (Int64.unsigned (List.nth j ys Int64.zero) mod
                   2 ^ (Int64.unsigned f mod 32))%Z by exact: mask_and.
      have [Lx Vx] := low_limbs ys xs' j (Int64.unsigned f mod 32) w Hy Ly Hj Hm Hl
        (fun p Hp => Hlo p ltac:(rewrite -/nk Ek; lia)) Hw.
      exists xs'; repeat split => //.
      rewrite Vx ExpModel.lowE; first lia.
      congr (_ mod 2 ^ _)%Z.
      rewrite /j Z2Nat.id; first lia.
      have := Z.div_mod (Int64.unsigned f) 32 ltac:(lia); lia.
Qed.
