(** * The two entry points of exp100, on the reals

    A run of the Capla [exp_encl_bits] that returns 0 gives an enclosure
    of exp x; a run of [maybe_hard_bits] that returns 0 says that x is not
    hard to round, x being the double of the bits [xb].  The pieces:
    [exp_encl_bits_spec] and [maybe_hard_bits_spec] (what the program
    computes, ExpTopProof.v) and [exp_encl_ok] and [maybe_hard_ok] (the
    reals, ExpSpec.v). *)

From Stdlib Require Import Reals Lra.
Require Flocq.Core.Core.
From Exp100 Require ExpBits ExpHard ExpSpec.

From Stdlib Require Import BinNums ZArith List Lia Utf8.
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
(* STUB-BEGIN *)
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
(* STUB-END *)
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** The return codes of the model *)

Lemma exp_encl_Z_rc xb rc :
  ExpModel.exp_encl_Z xb = inl rc -> (1 <= rc <= 3)%Z.
Proof.
rewrite /ExpModel.exp_encl_Z.
case Hc: (ExpModel.core_Z xb) => [r|[y hN]] // [<-].
exact: ExpModelBounds.core_Z_rc Hc.
Qed.

Lemma maybe_hard_Z_range xb : (0 <= ExpModel.maybe_hard_Z xb <= 1)%Z.
Proof.
rewrite /ExpModel.maybe_hard_Z.
case: (ExpModel.core_Z xb) => [r|[y hN]]; first lia.
rewrite /ExpModel.decide_Z; cbv zeta.
by repeat match goal with |- context [if ?b then _ else _] => case: b end;
  lia.
Qed.

(** ** The theorems *)

(* |exp x - M 2^s| <= D 2^s, x being the double of the bits xb *)
Definition encl (xb M s : Z) : Prop :=
  Rle (Rabs (Rminus (exp (ExpBits.xreal xb))
          (Rmult (IZR M) (Raux.bpow Zaux.radix2 s))))
      (Rmult (IZR ExpModel.D) (Raux.bpow Zaux.radix2 s)).

(* returns 0 only when x is not hard to round *)
Theorem maybe_hard_bits_real xb Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa ->
  eval_funcall ge (Internal maybe_hard_bits188) [Vint64 xb; Ta; Ca; L2a; RMa]
    e1 (Some result) ->
  exists r, result = Vint64 r /\ (0 <= Int64.unsigned r <= 1)%Z /\
    (Int64.unsigned r = 0%Z ->
       ~ ExpHard.hard (ExpBits.xreal (Int64.unsigned xb))).
Proof.
move=> Ht Hrun.
have -> := maybe_hard_bits_spec xb Ta Ca L2a RMa e1 result Ht Hrun.
have Hr := maybe_hard_Z_range (Int64.unsigned xb).
have Hu : Int64.unsigned
            (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))) =
          ExpModel.maybe_hard_Z (Int64.unsigned xb).
  by apply: Int64.unsigned_repr; change Int64.max_unsigned with
    (2 ^ 64 - 1)%Z; lia.
eexists; split; first reflexivity.
rewrite Hu; split => // H0.
apply: ExpSpec.maybe_hard_ok => //.
by have := Int64.unsigned_range xb; change Int64.modulus with (2 ^ 64)%Z.
Qed.

(* returns 0 only with an enclosure of exp x on (M, s) *)
Theorem exp_encl_bits_real xb ms ss Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa -> length ms = 3%nat -> length ss = 1%nat ->
  eval_funcall ge (Internal exp_encl_bits155)
    [Vint64 xb; Varr (map Vint64 ms); Varr (map Vint64 ss); Ta; Ca; L2a; RMa]
    e1 (Some result) ->
  exists rc, result = Vint64 rc /\ (0 <= Int64.unsigned rc <= 3)%Z /\
    (Int64.unsigned rc = 0%Z ->
       exists ms' s,
         e1!(param 1 exp_encl_bits155) = Some (Varr (map Vint64 ms')) /\
         length ms' = 3%nat /\
         e1!(param 2 exp_encl_bits155) = Some (Varr [Vint64 s]) /\
         encl (Int64.unsigned xb) (valW (map Int64.unsigned ms'))
           (Int64.signed s)).
Proof.
move=> Ht Hms Hss Hrun.
have [rc [-> [Hnz Hz]]] :=
  exp_encl_bits_spec xb ms ss Ta Ca L2a RMa e1 result Ht Hms Hss Hrun.
have Hxb : (0 <= Int64.unsigned xb < 2 ^ 64)%Z.
  by have := Int64.unsigned_range xb; change Int64.modulus with (2 ^ 64)%Z.
exists rc; split => //; split.
  case: (Z.eq_dec (Int64.unsigned rc) 0) => [->|Hn]; first lia.
  by have := exp_encl_Z_rc _ _ (Hnz Hn); lia.
move=> /Hz [ms' [s [H1 [H2 [H3 He]]]]].
exists ms', s; do 3 (split => //).
exact: ExpSpec.exp_encl_ok He.
Qed.

Print Assumptions maybe_hard_bits_real.
Print Assumptions exp_encl_bits_real.
