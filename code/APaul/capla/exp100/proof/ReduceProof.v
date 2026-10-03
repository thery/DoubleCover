(** * mul_ln2, guess_n: the specs (task T7) *)

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
Require Import Exp100Capla.GroupALemmas Exp100Capla.ReduceLemmas.
Require Import Exp100Capla.NumMulProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Section Reduce.

(* The spec of num_mul_small (NumMulProof.v), as a hypothesis. *)
Hypothesis num_mul_small_spec : forall ps xs w e1 result,
  length ps = 7%nat -> length xs = 6%nat -> limbs xs ->
  (Int64.unsigned w < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal num_mul_small43)
    [Varr (map Vint64 ps); Varr (map Vint64 xs); Vint64 w] e1 (Some result) ->
  exists ps', e1!(param 0 num_mul_small43) = Some (Varr (map Vint64 ps')) /\
    length ps' = 7%nat /\ limbs ps' /\
    val32 ps' = (val32 xs * Int64.unsigned w)%Z.

(* q = floor(n LN2 / 2^32), for n < 2^32 *)
Lemma mul_ln2_gen qs n e1 result :
  length qs = 6%nat -> (Int64.unsigned n < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal mul_ln2101)
    [Varr (map Vint64 qs); Vint64 n; Varr (map Vint64 LN2w)] e1 (Some result) ->
  exists qs', e1!(param 0 mul_ln2101) = Some (Varr (map Vint64 qs')) /\
    length qs' = 6%nat /\ limbs qs' /\
    val32 qs' = ExpModel.q (Int64.unsigned n).
Proof.
  move=> Hq Hn.
  have [HlL [LL HvL]] := LN2w_num.
  intro_eval_funcall mul_ln2101 out se1 exec.
  Opaque LN2w.
  apply_WP_stmt exec out e1 se1.
  name_var "q" Q.
  name_var "p" PP.
  name_var "i" I.
  repeat prog.
  move=> _ _ CALL.
  have [ps [E1 [Hlp [Lp Vp]]]] :=
    num_mul_small_spec (repeat Int64.zero 7) LN2w n _ _ (repeat_length _ _)
      HlL LL Hn CALL.
  tidy; clear CALL.
  repeat prog.
  rewrite E1; simplWP; repeat prog.
  (* after k steps: q[0..k-1] = p[1..k] *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k qs',
      e!I = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      e!Q = Some (Varr (map Vint64 qs')) /\ length qs' = 6%nat /\
      (forall j, (j < nat_of k)%coq_nat ->
         List.nth j qs' Int64.zero = List.nth (S j) ps Int64.zero).
  exists Inv; split.
  - exists (Int64.repr 0), qs.
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & qs' & [= ->] & Hk6 & [= ->] & Hl & Hlo) => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      have Hk1' : Z.to_nat (Int64.unsigned (Int64.add k (Int64.repr 1))) = S nk.
      { exact: Hk1. }
      rewrite Hk1'.
      rewrite nth_map_V64; first by rewrite length_map Hlp; lia.
      change (Z.to_nat (Int64.unsigned k)) with nk.
      exists (Int64.add k (Int64.repr 1)),
        (replace nk qs' (List.nth (S nk) ps Int64.zero)).
      rewrite Hk1 replace_map; repeat split => //.
      all: first [ clia k | by rewrite replace_length | idtac ].
      move=> j Hj.
      have [Hj'|->] : (j < nk)%coq_nat \/ j = nk by lia.
      * rewrite nth_replace_other; try lia; apply: Hlo; lia.
      * by rewrite nth_replace_same ?Hl.
    + have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      repeat prog.
      have Eq : qs' = skipn 1 ps.
      { apply: copy_shift => // j Hj; apply: Hlo; rewrite -/nk Ek; lia. }
      exists qs'; repeat split => //.
      * rewrite Eq; exact: limbs_skipn1.
      * rewrite Eq; exact: mul_ln2_value.
Qed.

(* the first guess of n: floor(X INV / 2^185) *)
Lemma guess_n_gen xs e1 result :
  length xs = 6%nat -> limbs xs ->
  eval_funcall ge (Internal guess_n105) [Varr (map Vint64 xs)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.guess (val32 xs))).
Proof.
  move=> Hx Lx.
  have [EI HI] := INV_word.
  have HI' : (Int64.unsigned (Int64.repr 3098164009) < 2 ^ limb_bits)%Z
    by rewrite EI.
  intro_eval_funcall guess_n105 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  apply_WP_stmt exec out e1 se1.
  name_var "p" PP.
  repeat prog.
  move=> _ _ CALL.
  have [ps [E1 [Hlp [Lp Vp]]]] :=
    num_mul_small_spec (repeat Int64.zero 7) xs _ _ _ (repeat_length _ _)
      Hx Lx HI' CALL.
  tidy; clear CALL.
  repeat prog.
  rewrite E1; simplWP; repeat prog.
  change (Z.to_nat (Int64.unsigned (Int64.repr 5))) with 5%nat.
  change (Z.to_nat (Int64.unsigned (Int64.repr 6))) with 6%nat.
  rewrite nth_map_V64; first (rewrite length_map Hlp; lia).
  rewrite nth_map_V64; first (rewrite length_map Hlp; lia).
  wsimpl.
  move=> ->; rewrite bits185w //.
  by rewrite (guess_value ps xs) // Vp EI.
Qed.

End Reduce.

(* q = floor(n LN2 / 2^32), for n < 2^32 *)
Theorem mul_ln2_spec qs n e1 result :
  length qs = 6%nat -> (Int64.unsigned n < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal mul_ln2101)
    [Varr (map Vint64 qs); Vint64 n; Varr (map Vint64 LN2w)] e1 (Some result) ->
  exists qs', e1!(param 0 mul_ln2101) = Some (Varr (map Vint64 qs')) /\
    length qs' = 6%nat /\ limbs qs' /\
    val32 qs' = ExpModel.q (Int64.unsigned n).
Proof. exact: (mul_ln2_gen num_mul_small_spec). Qed.

(* the first guess of n: floor(X INV / 2^185) *)
Theorem guess_n_spec xs e1 result :
  length xs = 6%nat -> limbs xs ->
  eval_funcall ge (Internal guess_n105) [Varr (map Vint64 xs)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.guess (val32 xs))).
Proof. exact: (guess_n_gen num_mul_small_spec). Qed.
