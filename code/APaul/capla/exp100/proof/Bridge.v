(** * From Capla's limbs to the shared model

    Capla holds a number as a list of int64 ([val32], [limbs] of
    ExpBase.v); the shared files hold it as a list of Z ([valZ], [limb] of
    ExpNum.v).  The two meet through [map Int64.unsigned]: after one
    rewrite, every lemma of ExpLimbs.v applies to Capla's lists. *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers.
Require Import Exp100Capla.ExpBase.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import WP ZifyIntegers ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Section Bridge.
Transparent Int64.unsigned Int64.repr.

(* The number of a list of words is the number of their values. *)
Lemma val32_valZ l : val32 l = valZ (map Int64.unsigned l).
Proof. by elim: l => [|x l IH] //=; rewrite IH. Qed.

(* The base of k limbs, as the shared files write it. *)
Lemma base32_limb k : base32 k = limb_base k.
Proof. by []. Qed.

(* Limb p of the values is the value of limb p. *)
Lemma nth_unsigned l p :
  List.nth p (map Int64.unsigned l) 0%Z =
  Int64.unsigned (List.nth p l Int64.zero).
Proof. by rewrite -(List.map_nth Int64.unsigned). Qed.

(* Every word is a limb exactly when every value is a limb. *)
Lemma limbs_Forall l : limbs l <-> Forall limb (map Int64.unsigned l).
Proof.
  split=> H.
  - apply/Forall_forall => y /in_map_iff [x [<- /(In_nth _ _ Int64.zero)]].
    move=> [p [_ <-]]; have := H p.
    have := Int64.unsigned_range (List.nth p l Int64.zero).
    rewrite /limb /limb_bits; lia.
  - move=> p; rewrite -nth_unsigned.
    case: (Nat.lt_ge_cases p (length (map Int64.unsigned l))) => Hp.
    + move/Forall_forall: H => /(_ _ (nth_In _ 0%Z Hp)).
      rewrite /limb /limb_bits; lia.
    + rewrite nth_overflow //; lia.
Qed.

End Bridge.

(* Writing x at k < length l: the low k words, x, then the others. *)
Lemma replace_split {A : Type} (l : list A) k x : (k < length l)%coq_nat ->
  replace k l x = (firstn k l ++ x :: skipn (S k) l)%list.
Proof. elim: l k => [|y l IH] [|k] //= H; try lia; rewrite IH //; lia. Qed.

(* The values after a write, in the shape of valZ_upd. *)
Lemma replace_unsigned l k x : (k < length l)%coq_nat ->
  map Int64.unsigned (replace k l x) =
  (firstn k (map Int64.unsigned l) ++ Int64.unsigned x ::
   skipn (S k) (map Int64.unsigned l))%list.
Proof.
  move=> H; rewrite replace_split // map_app firstn_map skipn_map //.
Qed.

(* Tests: two facts of ExpBase.v, read off ExpLimbs.v. *)
Lemma val32_app' l1 l2 :
  val32 (l1 ++ l2)%list = (val32 l1 + base32 (length l1) * val32 l2)%Z.
Proof. by rewrite !val32_valZ map_app valZ_app length_map base32_limb. Qed.

Lemma val32_firstn_S' l k :
  (k < length l)%coq_nat ->
  val32 (firstn (S k) l) =
  (val32 (firstn k l) + base32 k * Int64.unsigned (List.nth k l Int64.zero))%Z.
Proof.
  move=> H; rewrite !val32_valZ -!firstn_map valZ_firstn_S ?length_map //.
  by rewrite nth_unsigned base32_limb.
Qed.
