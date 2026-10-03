(** * Common ground for the proofs of the Capla exp100 (../exp100.b)

    The program as a Rocq term ([exp100.v], made by [ccomp -dcaplarocq]),
    and the number held by a list of limbs of 32 bits, each in a word of
    64 bits, the least significant first. *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Export Types Ops SyntaxCommon L1.
Require Export Exp100Capla.exp100.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Definition ge := genv_of_program program.

Definition nat_of (x : int64) : nat := Z.to_nat (Int64.unsigned x).

(* The number a list of limbs stands for. *)
Fixpoint val32 (l : list int64) : Z :=
  match l with [] => 0%Z | x :: l => (Int64.unsigned x + 2 ^ 32 * val32 l)%Z end.

(* Every limb is below 2^32. *)
Definition limbs (l : list int64) : Prop :=
  forall p, (Int64.unsigned (List.nth p l Int64.zero) < 2 ^ 32)%Z.

Definition base32 (k : nat) : Z := (2 ^ (32 * Z.of_nat k))%Z.
Arguments base32 : simpl never.

Lemma base32_0 : base32 0 = 1%Z.
Proof. by []. Qed.

Lemma base32S k : base32 (S k) = (base32 k * 2 ^ 32)%Z.
Proof. rewrite /base32 -Z.pow_add_r; try lia; f_equal; lia. Qed.

Lemma base32_pos k : (0 < base32 k)%Z.
Proof. rewrite /base32; apply Z.pow_pos_nonneg; lia. Qed.

Lemma val32_app l1 l2 :
  val32 (l1 ++ l2)%list = (val32 l1 + base32 (length l1) * val32 l2)%Z.
Proof.
  elim: l1 => [|x l1 IH]; cbn [val32 app length].
  - by rewrite base32_0 Z.mul_1_l.
  - rewrite IH base32S; ring.
Qed.

Lemma val32_nonneg l : (0 <= val32 l)%Z.
Proof.
  elim: l => [|x l IH]; cbn [val32]; first lia.
  have := Int64.unsigned_range x; lia.
Qed.

Lemma val32_bound l : limbs l -> (val32 l < base32 (length l))%Z.
Proof.
  elim: l => [|x l IH] Hl; cbn [val32 length]; first by rewrite base32_0; lia.
  have Hx := Hl 0%nat; cbn [List.nth] in Hx; have Hl' : limbs l by move=> p; apply: (Hl (S p)).
  have := IH Hl'; rewrite base32S; nia.
Qed.

Lemma firstn_S {A : Type} (l : list A) k d :
  (k < length l)%coq_nat -> firstn (S k) l = (firstn k l ++ [List.nth k l d])%list.
Proof.
  elim: l k => [|y l IH] [|k] /= H; try lia; first by [].
  rewrite -(IH k) //; lia.
Qed.

Lemma val32_firstn_S l k :
  (k < length l)%coq_nat ->
  val32 (firstn (S k) l) =
  (val32 (firstn k l) + base32 k * Int64.unsigned (List.nth k l Int64.zero))%Z.
Proof.
  move=> H; rewrite (firstn_S _ _ Int64.zero) // val32_app length_firstn /=.
  have -> : Init.Nat.min k (length l) = k by lia.
  lia.
Qed.

Lemma nth_map_V64 (l : list int64) k :
  (k < length (map Vint64 l))%coq_nat ->
  List.nth k (map Vint64 l) Vundef = Vint64 (List.nth k l Int64.zero).
Proof.
  rewrite length_map => H.
  rewrite (List.nth_indep _ Vundef (Vint64 Int64.zero)) ?length_map //.
  by rewrite List.map_nth.
Qed.

Lemma replace_map {A B : Type} (f : A -> B) k l x :
  replace k (map f l) (f x) = map f (replace k l x).
Proof. by elim: l k => [|y l IH] [|k] //=; rewrite IH. Qed.

Lemma replace_length {A : Type} (l : list A) k x :
  length (replace k l x) = length l.
Proof. by elim: l k => [|y l IH] [|k] //=; rewrite IH. Qed.

Lemma nth_replace_same {A : Type} (l : list A) k x d :
  (k < length l)%coq_nat -> List.nth k (replace k l x) d = x.
Proof. elim: l k => [|y l IH] [|k] //= H; try lia; apply IH; lia. Qed.

Lemma nth_replace_other {A : Type} (l : list A) k p x d :
  p <> k -> List.nth p (replace k l x) d = List.nth p l d.
Proof.
  elim: l k p => [|y l IH] [|k] [|p] //= H; apply IH; lia.
Qed.

Lemma firstn_replace {A : Type} (l : list A) k x :
  firstn k (replace k l x) = firstn k l.
Proof. by elim: l k => [|y l IH] [|k] //=; rewrite IH. Qed.


Section Words.
Transparent Int64.modu Int64.repr Int64.unsigned Int.repr Int.unsigned Int.modu.

(* The low limb of a word: c & (2^32 - 1). *)
Lemma and_mask (c : int64) :
  Int64.unsigned (Int64.and c (Int64.repr 4294967295)) =
  (Int64.unsigned c mod 2 ^ 32)%Z.
Proof.
  have -> : Int64.repr 4294967295 =
            Int64.sub (Int64.repr 4294967296) Int64.one by [].
  rewrite -(Int64.modu_and _ _ (Int64.repr 32)) //.
  have E : Int64.unsigned (Int64.repr 4294967296) = (2 ^ 32)%Z by [].
  rewrite /Int64.modu E Int64.unsigned_repr //.
  have := Int64.unsigned_range c.
  have := Z.mod_pos_bound (Int64.unsigned c) (2 ^ 32) ltac:(lia).
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* The carry of a word: c >> 32. *)
Lemma shru32 (c : int64) :
  Int64.unsigned (Int64.shru' c (Int.modu (Int.repr 32) Int64.iwordsize')) =
  (Int64.unsigned c / 2 ^ 32)%Z.
Proof.
  have -> : Int.modu (Int.repr 32) Int64.iwordsize' = Int.repr 32 by [].
  have E : Int.unsigned (Int.repr 32) = 32%Z by [].
  rewrite /Int64.shru' E Z.shiftr_div_pow2; lia.
Qed.

End Words.
