(** * maybe_hard_bits, exp_encl_bits: the specs (task T13) *)

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
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* The filter: maybe_hard_Z. *)
Theorem maybe_hard_bits_spec xb Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa ->
  eval_funcall ge (Internal maybe_hard_bits188) [Vint64 xb; Ta; Ca; L2a; RMa]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))).
Admitted.

(* The return code and, on success, M (3 words) and s as exp_encl_Z gives
   them. *)
Theorem exp_encl_bits_spec xb ms ss Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa -> length ms = 3%nat -> length ss = 1%nat ->
  eval_funcall ge (Internal exp_encl_bits155)
    [Vint64 xb; Varr (map Vint64 ms); Varr (map Vint64 ss); Ta; Ca; L2a; RMa]
    e1 (Some result) ->
  exists rc, result = Vint64 rc /\
    (Int64.unsigned rc <> 0%Z ->
       ExpModel.exp_encl_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0%Z ->
       exists ms' s,
         e1!(param 1 exp_encl_bits155) = Some (Varr (map Vint64 ms')) /\
         length ms' = 3%nat /\
         e1!(param 2 exp_encl_bits155) = Some (Varr [Vint64 s]) /\
         ExpModel.exp_encl_Z (Int64.unsigned xb) =
           inr (valW (map Int64.unsigned ms'), Int64.signed s)).
Admitted.
