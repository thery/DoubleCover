Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Exp100Capla.ExpBase.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.

(* WP's rule for alloc fills the array with defval (Tarr u64) = Vundef,
   the semantics with default_value u64 = Vint64 0: WP_sound gives False. *)
Lemma WP_sound_False : False.
Proof.
  set f := num_mulshr59.
  set i := 45%positive.
  set sz := Econst (Cint64 Unsigned (Int64.repr 12)).
  set Q := fun (o : outcome) (e2 : env) (se2 : senv) =>
    e2 ! i = Some (Varr (repeat (defval (Tarr u64)) 12)).
  have EX : exec_stmt ge (eval_funcall ge) f (PTree.empty _) (PTree.empty _)
              (PTree.empty _) (Salloc i sz)
              (env_alloc (PTree.empty _) i (Vint64 Int64.zero) 12)
              (senv_alloc (PTree.empty _) i (Int64.repr 12)) Out_normal.
  { change (env_alloc (PTree.empty value) i (Vint64 Int64.zero) 12) with
      (env_alloc (PTree.empty value) i (Vint64 Int64.zero)
         (Z.to_nat (Int64.unsigned (Int64.repr 12)))).
    apply: (exec_alloc _ _ _ _ _ _ _ u64).
    all: try by vm_compute.
    all: try by constructor. }
  have W : WP program f (Salloc i sz) Q (PTree.empty _) (PTree.empty _).
  { rewrite /=. unlock_let. unlock_let. rewrite /Q. by vm_compute. }
  have := WP_sound program _ _ _ _ _ _ _ _ _ _ W EX.
  rewrite /Q /env_alloc PTree.gss.
  move=> /(_ ltac:(discriminate)).
  by vm_compute.
Qed.
Print Assumptions WP_sound_False.
