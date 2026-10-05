(** * num_lt: the spec (task T4) *)

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

(* a < b *)
Theorem num_lt_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs xs -> limbs ys ->
  eval_funcall ge (Internal num_lt35)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  result = Vbool (val32 xs <? val32 ys)%Z.
Proof.
  move=> Hx Hy Lx Ly.
  intro_eval_funcall num_lt35 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  apply_WP_stmt exec out e1 se1.
  name_var "k" K.
  repeat prog.
  (* after k steps: the top k limbs of a and b agree *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k,
      e!K = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      (forall p, (6 - nat_of k <= p)%coq_nat -> (p < 6)%coq_nat ->
         List.nth p xs Int64.zero = List.nth p ys Int64.zero).
  exists Inv; split.
  - exists (Int64.repr 0).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & [= ->] & Hk6 & Htop) => /=.
    tidy.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      have Hi : Z.to_nat (Int64.unsigned (Int64.sub (Int64.repr 5) k)) =
                (5 - nk)%coq_nat.
      { rewrite /nk /nat_of; move: Hk; rewrite /nk /nat_of; clia k. }
      rewrite Hi.
      rewrite !nth_map_V64 ?length_map; try lia.
      wsimpl.
      set a := List.nth (5 - nk) xs Int64.zero.
      set b := List.nth (5 - nk) ys Int64.zero.
      have Ht : forall p, (5 - nk < p)%coq_nat -> (p < 6)%coq_nat ->
                  List.nth p xs Int64.zero = List.nth p ys Int64.zero.
      { move=> p Hp1 Hp2; apply: Htop => //; lia. }
      case L1: (Int64.ltu a b); simplWP; repeat prog.
      * (* a_i < b_i: return true *)
        have Hab : (Int64.unsigned a < Int64.unsigned b)%Z.
        { by move: L1; rewrite /Int64.ltu; case: zlt. }
        have Hlt := val32_lt_top xs ys (5 - nk) Hx Hy Lx Ly ltac:(lia) Ht Hab.
        by move=> ->; rewrite (proj2 (Z.ltb_lt _ _) Hlt).
      * have Hab : (Int64.unsigned b <= Int64.unsigned a)%Z.
        { move: L1; rewrite /Int64.ltu; case: zlt => // H _; lia. }
        rewrite Hi.
        rewrite !nth_map_V64 ?length_map; try lia.
        wsimpl.
        case L2: (Int64.ltu b a); simplWP; repeat prog.
        -- (* a_i > b_i: return false *)
           have Hba : (Int64.unsigned b < Int64.unsigned a)%Z.
           { by move: L2; rewrite /Int64.ltu; case: zlt. }
           have Ht' : forall p, (5 - nk < p)%coq_nat -> (p < 6)%coq_nat ->
                        List.nth p ys Int64.zero = List.nth p xs Int64.zero.
           { by move=> p Hp1 Hp2; rewrite Ht. }
           have Hlt := val32_lt_top ys xs (5 - nk) Hy Hx Ly Lx ltac:(lia) Ht' Hba.
           move=> ->; congr Vbool; symmetry; apply/Z.ltb_ge; lia.
        -- (* a_i = b_i: next limb *)
           have Hba : (Int64.unsigned a <= Int64.unsigned b)%Z.
           { move: L2; rewrite /Int64.ltu; case: zlt => // H _; lia. }
           have Eab : a = b.
           { rewrite -(Int64.repr_unsigned a) -(Int64.repr_unsigned b).
             congr Int64.repr; lia. }
           exists (Int64.add k (Int64.repr 1)); rewrite Hk1; repeat split => //.
           ++ clia k.
           ++ move=> p Hp1 Hp2.
              have [Hp|Hp] : (p = 5 - nk)%coq_nat \/ (5 - nk < p)%coq_nat by lia.
              ** by rewrite Hp.
              ** exact: Ht.
    + (* all limbs agree: return false *)
      have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      repeat prog.
      have Exy : xs = ys.
      { apply: list6_ext => // p Hp; apply: Htop => //; rewrite -/nk Ek; lia. }
      by move=> ->; rewrite Exy Z.ltb_irrefl.
Qed.
