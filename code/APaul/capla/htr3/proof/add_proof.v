(* Correctness of htr3.c's multi-limb addition, compiled by Capla (add.b). *)
Require Import BinNums ZArith String List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
(* Load before WP because WP introduces notations that clash with it. *)
Load "add.v".
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

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

Section Proof.
Let ge := genv_of_program program.

Theorem add_spec:
  ∀ xa xb n e1 result,
    let nn := Z.to_nat (Int64.unsigned n) in
    eval_funcall ge (Internal add10)
      [Varr (map Vint64 xa); Varr (map Vint64 xb); Vint64 n] e1 (Some result) ->
    ∃ xa',
      e1!(param 0 add10) = Some (Varr (map Vint64 xa')) /\
      length xa' = length xa /\
      (nn <= length xa)%coq_nat /\ (nn <= length xb)%coq_nat /\
      skipn nn xa' = skipn nn xa /\
      val (firstn nn xa') =
      ((val (firstn nn xa) + val (firstn nn xb)) mod base nn)%Z.
Proof.
  intros *.
  intro_eval_funcall add10 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "a" A.
  name_var "cy" CY.
  repeat prog.
  pose Inv := fun (e: env) (se: senv) =>
    ∃ k xa' c,
      e!i = Some (Vint64 k) /\
      ~~ Int64.ltu n k /\
      let nk := Z.to_nat (Int64.unsigned k) in
      e!A = Some (Varr (map Vint64 xa')) /\
      e!CY = Some (Vint64 c) /\
      (Int64.unsigned c <= 1)%Z /\
      length xa' = length xa /\
      (nk <= length xa)%coq_nat /\ (nk <= length xb)%coq_nat /\
      skipn nk xa' = skipn nk xa /\
      (val (firstn nk xa') + Int64.unsigned c * base nk =
       val (firstn nk xa) + val (firstn nk xb))%Z.
  exists Inv; split.
  - rewrite /Inv.
    exists (Int64.repr 0), xa, (Int64.repr 0).
    change (Z.to_nat (Int64.unsigned (Int64.repr 0))) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & xa' & c & [= ->] & ? & [= ->] & [= ->] & Hc & Hl & Hka & Hkb & LV & HV) => /=.
    set nk := Z.to_nat (Int64.unsigned k).
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hnka : (nk < length xa')%coq_nat.
      { match goal with H : (_ < length (map Vint64 xa'))%coq_nat |- _ =>
          rewrite length_map in H; exact H end. }
      have Hnkb : (nk < length xb)%coq_nat.
      { match goal with H : (_ < length (map Vint64 xb))%coq_nat |- _ =>
          rewrite length_map in H; exact H end. }
      have Hk1 : Z.to_nat (Int64.unsigned (Int64.add k (Int64.repr 1))) = S nk.
      { rewrite /nk; clia k. }
      rewrite ?nth_map_V64 //=.
      case C1: Int64.ltu; simplWP; repeat prog.
      * rewrite /sem_binarith /sem_cast /sem_cmpu /= -/nk.
        exists (Int64.add k (Int64.repr 1)),
          (replace nk xa' (Int64.add (List.nth nk xa' Int64.zero)
                             (Int64.add (List.nth nk xb Int64.zero) c))),
          Int64.one.
        rewrite Hk1 replace_map; repeat split => //.
        -- clia n, k.
        -- by rewrite replace_length.
        -- lia.
        -- by rewrite skipn_replace; apply skipn_S.
        -- apply step_val => //.
           by have := carry_step (List.nth nk xa' Int64.zero) (List.nth nk xb Int64.zero) c Hc; rewrite /= C1.
      * rewrite /sem_binarith /sem_cast /sem_cmpu /= -/nk.
        rewrite nth_replace_same ?length_map //=.
        exists (Int64.add k (Int64.repr 1)),
          (replace nk xa' (Int64.add (List.nth nk xa' Int64.zero)
                             (Int64.add (List.nth nk xb Int64.zero) c))).
        eexists.
        rewrite Hk1 replace_map; repeat split => //.
        -- clia n, k.
        -- case: Int64.ltu => /=; lia.
        -- by rewrite replace_length.
        -- lia.
        -- by rewrite skipn_replace; apply skipn_S.
        -- apply step_val => //.
           have := carry_step (List.nth nk xa' Int64.zero) (List.nth nk xb Int64.zero) c Hc; rewrite /= C1 /=.
           by case: Int64.ltu => /=.
    + have Ek : k = n by clia k.
      subst k.
      exists xa'; repeat split => //.
      apply: (Z.mod_unique_pos _ _ (Int64.unsigned c)); last by rewrite /nn -HV; ring.
      have := val_bound (firstn nn xa'); rewrite length_firstn.
      have -> : Init.Nat.min nn (length xa') = nn by lia.
      lia.
Qed.

End Proof.
Print Assumptions add_spec.
