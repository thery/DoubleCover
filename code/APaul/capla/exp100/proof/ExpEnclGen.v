(** * exp_encl_bits, with exp_core as a hypothesis

    exp_encl_bits calls exp_core (ExpCoreProof.v), used here through its
    spec, stated as a Section hypothesis.  ExpTopProof.v instantiates it. *)

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
Require Import Exp100Capla.GroupALemmas Exp100Capla.TopLemmasCapla.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.


(** ** Symbolic execution one statement at a time (as in ExpCoreProof.v) *)

(* WP, kept folded by simpl. *)
Definition WPc := WP.
Arguments WPc : simpl never.

(* The first statement of a sequence, with the rest hidden. *)
Lemma WP_seq_c p f s1 s2 Q e se :
  WP p f s1 (fun out => match out with
    | Out_normal => WPc p f s2 Q
    | Out_error => fun _ _ => True
    | Out_exit n => Q (Out_exit n)
    | Out_return r => Q (Out_return r)
    end) e se ->
  WP p f (Sseq s1 s2) Q e se.
Proof. by []. Qed.

Lemma WPcE : WPc = WP.
Proof. by []. Qed.

Opaque WPc.

(* a statement that calls no function and tests nothing *)
Ltac nocall a :=
  lazymatch a with
  | context [Scall _ _ _] => fail
  | context [Sifthenelse _ _ _] => fail
  | _ => idtac
  end.

(* run the next statement when it calls no function and tests nothing *)
Ltac wpone := lazymatch goal with
  | |- WPc _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP
  | |- WPc _ _ ?a _ _ _ => nocall a; rewrite {1}WPcE -?lock; simplWP
  | |- WP _ _ (Sseq ?a _) _ _ _ =>
      nocall a; rewrite -?lock; apply: WP_seq_c; simplWP
  end.

(* run the statements up to a call or a test *)
Ltac wpauto := repeat (wpone; repeat prog).

(* enter the next statement, whatever it is *)
Ltac wpenter := lazymatch goal with
  | |- WPc _ _ (Sseq _ _) _ _ _ =>
      rewrite {1}WPcE -?lock; apply: WP_seq_c; simplWP; repeat prog
  | |- WPc _ _ _ _ _ _ => rewrite {1}WPcE -?lock; simplWP; repeat prog
  end.

(* split on the first test of the goal *)
Ltac wpcase B :=
  match goal with |- context [if ?b then _ else _] => case B: b end;
  rewrite -?lock; simplWP; repeat prog.

(* the head of a statement, for probes *)
Ltac shead a :=
  lazymatch a with
  | Sseq ?x _ => shead x
  | Scall _ ?f _ => idtac "call" f
  | Sletref _ (Scall _ ?f _) => idtac "letref-call" f
  | Sletref _ _ => idtac "letref"
  | Sifthenelse _ _ _ => idtac "if"
  | Sassign (?i, _) _ => idtac "assign" i
  | Sfree ?i => idtac "free" i
  | Salloc ?i _ => idtac "alloc" i
  | Sloop _ => idtac "loop"
  | Sblock _ => idtac "block"
  | Sreturn _ => idtac "return"
  | Sskip => idtac "skip"
  | _ => idtac "stmt"
  end.

(* the shape of the goal, for probes *)
Ltac summ := lazymatch goal with
  | |- WPc _ _ ?a _ _ _ => idtac "WPc"; shead a
  | |- WP _ _ ?a _ _ _ => idtac "WP"; shead a
  | |- (if ?b then _ else _) => idtac "IF"
  | |- let% _ := _ in _ => idtac "LET"
  | |- forall _, _ => idtac "FORALL"
  | |- ?a -> _ => idtac "ARROW"
  | |- exists _, _ => idtac "EXISTS"
  | |- _ = _ => idtac "EQ"
  | |- _ => idtac "OTHER"
  end.

Section Encl.

(* The spec of exp_core (ExpCoreProof.v). *)
Hypothesis exp_core_spec : forall xb ys hs Xs qs q1s rs hhs ts Ta Ca L2a RMa e1 result,
  tables_ok Ta Ca L2a RMa ->
  length ys = 6%nat -> length hs = 1%nat ->
  length Xs = 6%nat -> length qs = 6%nat -> length q1s = 6%nat ->
  length rs = 6%nat -> length hhs = 6%nat -> length ts = 6%nat ->
  eval_funcall ge (Internal exp_core138)
    [Vint64 xb; Varr (map Vint64 ys); Varr (map Vint64 hs);
     Varr (map Vint64 Xs); Varr (map Vint64 qs); Varr (map Vint64 q1s);
     Varr (map Vint64 rs); Varr (map Vint64 hhs); Varr (map Vint64 ts);
     Ta; Ca; L2a; RMa] e1 (Some result) ->
  exists rc, result = Vint64 rc /\
    (Int64.unsigned rc <> 0%Z ->
       ExpModel.core_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0%Z ->
       exists ys' hN,
         e1!(param 1 exp_core138) = Some (Varr (map Vint64 ys')) /\
         length ys' = 6%nat /\ limbs ys' /\
         e1!(param 2 exp_core138) = Some (Varr [Vint64 hN]) /\
         ExpModel.core_Z (Int64.unsigned xb) =
           inr (val32 ys', Int64.signed hN) /\
         arr6 (e1!(param 3 exp_core138)) /\ arr6 (e1!(param 4 exp_core138)) /\
         arr6 (e1!(param 5 exp_core138)) /\ arr6 (e1!(param 6 exp_core138))).

(* The return code and, on success, M (3 words) and s as exp_encl_Z gives
   them. *)
Lemma exp_encl_bits_gen xb ms ss Ta Ca L2a RMa e1 result :
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
Proof.
  move=> Htab Hm Hs.
  intro_eval_funcall exp_encl_bits155 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  pattern out, e1, se1.
  apply: (WP_sound _ _ _ _ _ _ _ _ _ _ _ _ exec); first (by destruct out).
  change (fn_body FUNC) with BODY; rewrite /BODY.
  wpauto.
  wpenter.
Admitted.

End Encl.
