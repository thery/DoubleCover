(** * Common ground for the proofs of the Capla htr3 (htr3.b)

    The program as a Rocq term ([htr3.v], made by [ccomp -dcaplarocq]),
    the numbers held by a flat array of words, and the list and carry
    lemmas shared by the proofs of the functions. *)

Require Import BinNums ZArith String List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Export Types Ops SyntaxCommon L1.
Require Export Htr3.htr3.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Require Export APaulRocq.HtrDefs.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* The global environment of the program. *)
Definition ge := genv_of_program program.

(* An unsigned 64-bit integer as a natural number. *)
Definition nat_of (x : int64) : nat := Z.to_nat (Int64.unsigned x).

(* The number a list of words stands for, least significant word first. *)
Fixpoint val (l : list int64) : Z :=
  match l with [] => 0%Z | x :: l => (Int64.unsigned x + 2 ^ 64 * val l)%Z end.

(* The weight of word k. *)
Definition base (k : nat) : Z := (2 ^ (64 * Z.of_nat k))%Z.
Arguments base : simpl never.

Section Arith.

Lemma base0 : base 0 = 1%Z.
Proof. by []. Qed.

Lemma baseS k : base (S k) = (base k * 2 ^ 64)%Z.
Proof. rewrite /base -Z.pow_add_r; try lia; f_equal; lia. Qed.

Lemma base_pos k : (0 < base k)%Z.
Proof. rewrite /base; apply Z.pow_pos_nonneg; lia. Qed.

Lemma val_app l1 l2 : val (l1 ++ l2)%list = (val l1 + base (length l1) * val l2)%Z.
Proof.
  elim: l1 => [|x l1 IH]; cbn [val app length].
  - by rewrite base0 Z.mul_1_l.
  - rewrite IH baseS; ring.
Qed.

Lemma val_bound l : (0 <= val l < base (length l))%Z.
Proof.
  elim: l => [|x l IH]; cbn [val length]; first by rewrite base0; lia.
  rewrite baseS; have := Int64.unsigned_range x.
  change Int64.modulus with (2 ^ 64)%Z; nia.
Qed.

(* The carry of one step of the loop is the true carry. *)
Lemma carry_step (a b c : int64) : (Int64.unsigned c <= 1)%Z ->
  let t := Int64.add b c in let s := Int64.add a t in
  (Int64.unsigned s + 2 ^ 64 * (if Int64.ltu t c || Int64.ltu s t then 1 else 0) =
   Int64.unsigned a + Int64.unsigned b + Int64.unsigned c)%Z.
Proof.
  move=> Hc t s; rewrite /s /t.
  case E1: (Int64.ltu _ c); case E2: (Int64.ltu _ _) => /=; lia.
Qed.

End Arith.

Section Lists.

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

Lemma skipn_replace {A : Type} (l : list A) k x :
  skipn (S k) (replace k l x) = skipn (S k) l.
Proof. by elim: l k => [|y l IH] [|k] //=; apply IH. Qed.

Lemma firstn_replace {A : Type} (l : list A) k x :
  firstn k (replace k l x) = firstn k l.
Proof. by elim: l k => [|y l IH] [|k] //=; rewrite IH. Qed.

Lemma firstn_S {A : Type} (l : list A) k d :
  (k < length l)%coq_nat -> firstn (S k) l = (firstn k l ++ [List.nth k l d])%list.
Proof.
  elim: l k => [|y l IH] [|k] /= H; try lia; first by [].
  rewrite -(IH k) //; lia.
Qed.

Lemma nth_skipn0 {A : Type} (l : list A) k d :
  List.nth k l d = List.nth 0 (skipn k l) d.
Proof. by elim: l k => [|x l IH] [|k] //=. Qed.

Lemma nth_skipn_eq {A : Type} (l1 l2 : list A) k d :
  skipn k l1 = skipn k l2 -> List.nth k l1 d = List.nth k l2 d.
Proof. by rewrite (nth_skipn0 l1) (nth_skipn0 l2) => ->. Qed.

Lemma skipn_S {A : Type} (l1 l2 : list A) k :
  skipn k l1 = skipn k l2 -> skipn (S k) l1 = skipn (S k) l2.
Proof. by rewrite -!(skipn_skipn 1 k) => ->. Qed.

(* One word more. *)
Lemma val_firstn_S l k :
  (k < length l)%coq_nat ->
  val (firstn (S k) l) =
  (val (firstn k l) + base k * Int64.unsigned (List.nth k l Int64.zero))%Z.
Proof.
  move=> H; rewrite (firstn_S _ _ Int64.zero) // val_app length_firstn /=.
  have -> : Init.Nat.min k (length l) = k by lia.
  lia.
Qed.

(* The invariant is kept by one step of the loop, on the words. *)
Lemma step_val xa xb xa' nk (c c' : int64) :
  (nk < length xa')%coq_nat -> (nk < length xb)%coq_nat ->
  skipn nk xa' = skipn nk xa ->
  (val (firstn nk xa') + Int64.unsigned c * base nk =
   val (firstn nk xa) + val (firstn nk xb))%Z ->
  let ak := List.nth nk xa' Int64.zero in
  let bk := List.nth nk xb Int64.zero in
  let s := Int64.add ak (Int64.add bk c) in
  (Int64.unsigned s + 2 ^ 64 * Int64.unsigned c' =
   Int64.unsigned ak + Int64.unsigned bk + Int64.unsigned c)%Z ->
  (val (firstn (S nk) (replace nk xa' s)) + Int64.unsigned c' * base (S nk) =
   val (firstn (S nk) xa) + val (firstn (S nk) xb))%Z.
Proof.
  move=> Ha Hb LV HV ak bk s Hs.
  have Ha' : (nk < length xa)%coq_nat.
  { have := f_equal (@length _) LV; rewrite !length_skipn; lia. }
  rewrite !val_firstn_S ?replace_length // firstn_replace nth_replace_same //.
  rewrite -(nth_skipn_eq _ _ _ _ LV) -/ak -/bk baseS.
  have := base_pos nk; nia.
Qed.

End Lists.


(* ** Coefficients of a flat array

   A flat array of words holds the coefficients B_0, B_1, ..., each of l
   words, the least significant first: B_i is the words i*l .. i*l + l - 1. *)

(* The words of B_i. *)
Definition coef (xs : list int64) (l i : nat) : list int64 :=
  firstn l (skipn (i * l) xs).

(* The number B_i. *)
Definition vcoef (xs : list int64) (l i : nat) : Z := val (coef xs l i).

(* The numbers B_0 .. B_(k-1). *)
Definition vcoefs (xs : list int64) (l k : nat) : list Z :=
  map (vcoef xs l) (seq 0 k).

(* Lists read from an offset. *)
Lemma nth_skipn_add {A : Type} (l : list A) n k d :
  List.nth k (skipn n l) d = List.nth (n + k) l d.
Proof. by elim: l n => [|x l IH] [|n] //=; case: k. Qed.

Lemma skipn_replace_add {A : Type} (l : list A) n k x :
  skipn n (replace (n + k) l x) = replace k (skipn n l) x.
Proof. by elim: l n => [|y l IH] [|n] //=; case: k. Qed.

Lemma nth_replace_other {A : Type} (l : list A) k p x d :
  p <> k -> List.nth p (replace k l x) d = List.nth p l d.
Proof.
  elim: l k p => [|y l IH] [|k] [|p] //= H; apply IH; lia.
Qed.
