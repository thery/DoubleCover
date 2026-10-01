(** * T3: difftab, the table of differences *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Htr3.HtrBase.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Require Import Htr3.SubwProof.

(* ** The differences, on integers *)

(* The sum of f t for t < m. *)
Definition sumZ (f : nat -> Z) (m : nat) : Z :=
  fold_right Z.add 0%Z (map f (seq 0 m)).

Lemma fold_addZ (l : list Z) a :
  fold_right Z.add a l = (fold_right Z.add 0 l + a)%Z.
Proof. elim: l => [|x l IH] /=; lia. Qed.

Lemma sumZ_S0 f m : sumZ f (S m) = (f 0%nat + sumZ (fun t => f (S t)) m)%Z.
Proof. by rewrite /sumZ /= -seq_shift map_map. Qed.

Lemma sumZ_Sr f m : sumZ f (S m) = (sumZ f m + f m)%Z.
Proof.
  by rewrite /sumZ seq_S map_app fold_right_app /= fold_addZ Z.add_0_r.
Qed.

Lemma sumZ_ext f g m : (forall t, (t < m)%coq_nat -> f t = g t) ->
  sumZ f m = sumZ g m.
Proof.
  move=> H; rewrite /sumZ; congr fold_right; apply: map_ext_in => t.
  rewrite in_seq => Ht; apply: H; lia.
Qed.

Lemma sumZ_add f g m :
  sumZ (fun t => f t + g t)%Z m = (sumZ f m + sumZ g m)%Z.
Proof. elim: m => [|m IH]; rewrite ?sumZ_Sr ?IH //; lia. Qed.

Lemma sumZ_opp f m : sumZ (fun t => - f t)%Z m = (- sumZ f m)%Z.
Proof. elim: m => [|m IH]; rewrite ?sumZ_Sr ?IH //; lia. Qed.

Lemma binom_gt n t : (n < t)%coq_nat -> binom n t = 0%Z.
Proof.
  elim: n t => [|n IH] [|t] /= H; try lia.
  rewrite !IH; lia.
Qed.

Lemma binom0 n : binom n 0 = 1%Z.
Proof. by case: n. Qed.

Lemma pow_m1S m : ((-1) ^ Z.of_nat m.+1 = - (-1) ^ Z.of_nat m)%Z.
Proof. rewrite Nat2Z.inj_succ Z.pow_succ_r; lia. Qed.

(* The a-th difference of x at n, by the recurrence. *)
Fixpoint dif (x : nat -> Z) (a n : nat) : Z :=
  match a with
  | O => x n
  | S a => (dif x a (S n) - dif x a n)%Z
  end.

(* The recurrence gives the sum with the binomial coefficients. *)
Lemma dif_sum x a n :
  dif x a n = sumZ (fun t =>
    (-1) ^ Z.of_nat (a - t)%coq_nat * binom a t * x (n + t)%coq_nat)%Z
    (S a).
Proof.
  elim: a n => [|a IH] n.
  - rewrite /sumZ /= Nat.add_0_r; by case: (x n).
  - rewrite [dif _ _ _]/= !IH (sumZ_S0 _ a.+1).
    (* Pascal's rule splits the sum in two. *)
    rewrite (sumZ_ext (fun t => _ * binom a.+1 t.+1 * _)%Z (fun t =>
      ((-1) ^ Z.of_nat (a - t)%coq_nat * binom a t * x (n.+1 + t)%coq_nat) +
      ((-1) ^ Z.of_nat (a - t)%coq_nat * binom a t.+1 *
         x (n + t.+1)%coq_nat))%Z).
    { move=> t Ht; have -> : (n.+1 + t)%coq_nat = (n + t.+1)%coq_nat by lia.
      have -> : (a.+1 - t.+1)%coq_nat = (a - t)%coq_nat by lia.
      rewrite [binom a.+1 _]/=; ring. }
    rewrite sumZ_add (sumZ_Sr (fun t => _ * binom a t.+1 * _)%Z)
      (binom_gt a a.+1); first lia.
    rewrite (sumZ_S0 (fun t => _ * binom a t * x (n + t)%coq_nat)%Z).
    rewrite (sumZ_ext
      (fun t => (-1) ^ Z.of_nat (a - t)%coq_nat * binom a t.+1 * _)%Z
      (fun t => - ((-1) ^ Z.of_nat (a - t.+1)%coq_nat * binom a t.+1 *
                   x (n + t.+1)%coq_nat))%Z).
    { move=> t Ht; have -> : (a - t)%coq_nat = (a - t.+1)%coq_nat.+1 by lia.
      by rewrite pow_m1S; ring. }
    rewrite sumZ_opp.
    have -> : (a.+1 - 0)%coq_nat = a.+1 by lia.
    have -> : (a - 0)%coq_nat = a by lia.
    rewrite pow_m1S; rewrite !binom0; ring.
Qed.

(* The difference of fdiff is the one of the recurrence. *)
Lemma fdiff_dif x k j : (j < k)%coq_nat ->
  fdiff (map x (seq 0 k)) j = dif x j 0.
Proof.
  move=> Hj; rewrite dif_sum /fdiff -/(sumZ _ _); apply: sumZ_ext => t Ht.
  rewrite (nth_indep _ 0%Z (x 0%nat)).
  { by rewrite length_map length_seq; lia. }
  by rewrite map_nth seq_nth; first lia.
Qed.

(* After a passes, B_p holds the difference of order min p a. *)
Definition stage (x : nat -> Z) (a p : nat) : Z :=
  dif x (Nat.min p a) (p - Nat.min p a)%coq_nat.

(* One step of pass a + 1, at p > a. *)
Lemma stage_step x a p : (a < p)%coq_nat ->
  (stage x a p - stage x a p.-1)%Z = stage x a.+1 p.
Proof.
  move=> H; rewrite /stage.
  have -> : Nat.min p a = a by lia.
  have -> : Nat.min p.-1 a = a by lia.
  have -> : Nat.min p a.+1 = a.+1 by lia.
  rewrite [dif _ a.+1 _]/=.
  have -> : (p - a)%coq_nat = (p - a.+1)%coq_nat.+1 by lia.
  by have -> : (p.-1 - a)%coq_nat = (p - a.+1)%coq_nat by lia.
Qed.

(* Pass a + 1 leaves B_p alone for p <= a. *)
Lemma stage_low x a p : (p <= a)%coq_nat -> stage x a.+1 p = stage x a p.
Proof.
  move=> H; rewrite /stage.
  have -> : Nat.min p a = p by lia.
  by have -> : Nat.min p a.+1 = p by lia.
Qed.

(* After p passes, B_p is the difference of order p at 0. *)
Lemma stage_end x a p : (p <= a)%coq_nat -> stage x a p = dif x p 0.
Proof.
  move=> H; rewrite /stage.
  have -> : Nat.min p a = p by lia.
  by rewrite Nat.sub_diag.
Qed.

(* ** Coefficients of a flat array *)

(* Two arrays that agree from n on have the same tail. *)
Lemma skipn_eq_nth (xs1 xs2 : list int64) n :
  length xs1 = length xs2 ->
  (forall q : nat, (n <= q)%coq_nat ->
     List.nth q xs1 Int64.zero = List.nth q xs2 Int64.zero) ->
  skipn n xs1 = skipn n xs2.
Proof.
  move=> Hl H; apply: (nth_ext _ _ Int64.zero Int64.zero).
  - by rewrite !length_skipn Hl.
  - move=> q Hq; rewrite !nth_skipn_add; apply: H; lia.
Qed.

(* Two arrays that agree on the words of B_p have the same B_p. *)
Lemma coef_eq_nth (xs1 xs2 : list int64) (L p : nat) :
  length xs1 = length xs2 ->
  (forall q : nat, (p * L <= q)%coq_nat -> (q < p * L + L)%coq_nat ->
     List.nth q xs1 Int64.zero = List.nth q xs2 Int64.zero) ->
  coef xs1 L p = coef xs2 L p.
Proof.
  move=> Hl H; rewrite /coef.
  apply: (nth_ext _ _ Int64.zero Int64.zero).
  - by rewrite !length_firstn; rewrite !length_skipn Hl.
  - move=> q; rewrite length_firstn length_skipn => Hq.
    rewrite !nth_firstn.
    case: Nat.ltb_spec => // Hq'; rewrite !nth_skipn_add; apply: H; lia.
Qed.

Lemma base_le n1 n2 : (n1 <= n2)%coq_nat -> (base n1 <= base n2)%Z.
Proof. move=> H; rewrite /base; apply: Z.pow_le_mono_r; lia. Qed.

(* B_p holds a number of l words. *)
Lemma vcoef_bound xs L p : (0 <= vcoef xs L p < base L)%Z.
Proof.
  rewrite /vcoef; have := val_bound (coef xs L p).
  have := base_le (length (coef xs L p)) L.
  rewrite /coef length_firstn; lia.
Qed.

(* ** Index arithmetic *)

(* B_j, for j < k, lies inside the array. *)
Lemma idx_bound (j k l m : int64) :
  (Int64.unsigned j < Int64.unsigned k)%Z ->
  (nat_of k * nat_of l <= nat_of m)%coq_nat ->
  (Int64.unsigned j * Int64.unsigned l + Int64.unsigned l <=
   Int64.unsigned m)%Z.
Proof.
  rewrite /nat_of => Hj Hk.
  have := Int64.unsigned_range j; have := Int64.unsigned_range k.
  have := Int64.unsigned_range l; have := Int64.unsigned_range m.
  move: Hj Hk; change Int64.modulus with (2 ^ 64)%Z.
  generalize (Int64.unsigned j) (Int64.unsigned k) (Int64.unsigned l)
    (Int64.unsigned m) => uj uk ul um Hj Hk *.
  move/Nat2Z.inj_le: Hk; rewrite Nat2Z.inj_mul; rewrite !Z2Nat.id; try lia.
  nia.
Qed.

(* The word index j * l does not wrap around. *)
Lemma nat_of_mul (j l : int64) :
  (Int64.unsigned j * Int64.unsigned l <= Int64.max_unsigned)%Z ->
  nat_of (Int64.mul j l) = (nat_of j * nat_of l)%coq_nat.
Proof.
  move=> H; have := Int64.unsigned_range j; have := Int64.unsigned_range l.
  rewrite /nat_of Int64_mul_inj Z.mod_small => *.
  - change Int64.max_unsigned with (2 ^ 64 - 1)%Z in H; lia.
  - rewrite Z2Nat.inj_mul //; lia.
Qed.

(* The two calls of the inner loop: B_j and B_(j-1), for 1 <= j < k. *)
Lemma idx_facts (j k l m : int64) :
  (1 <= Int64.unsigned j)%Z -> (Int64.unsigned j < Int64.unsigned k)%Z ->
  (nat_of k * nat_of l <= nat_of m)%coq_nat ->
  let JL := nat_of (Int64.mul j l) in
  JL = (nat_of j * nat_of l)%coq_nat /\
  (nat_of (Int64.mul (Int64.sub j (Int64.repr 1)) l) + nat_of l = JL)%coq_nat
  /\ (JL + nat_of l <= nat_of k * nat_of l)%coq_nat.
Proof.
  move=> H1 Hj Hk JL.
  have Hb := idx_bound j k l m Hj Hk.
  have Hm := Int64.unsigned_range m.
  have Hl := Int64.unsigned_range l.
  have Hs : Int64.unsigned (Int64.sub j (Int64.repr 1)) =
            (Int64.unsigned j - 1)%Z by clia j.
  have Hj0 := Int64.unsigned_range j.
  change Int64.modulus with (2 ^ 64)%Z in *.
  have E1 : JL = (nat_of j * nat_of l)%coq_nat.
  { apply: nat_of_mul; change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia. }
  have E2 : nat_of (Int64.mul (Int64.sub j (Int64.repr 1)) l) =
            (nat_of (Int64.sub j (Int64.repr 1)) * nat_of l)%coq_nat.
  { apply: nat_of_mul; rewrite Hs.
    change Int64.max_unsigned with (2 ^ 64 - 1)%Z; nia. }
  rewrite E2 E1; move: Hs; rewrite /nat_of => Hs; rewrite Hs.
  split => //; split; first by nia.
  have : (nat_of j < nat_of k)%coq_nat by rewrite /nat_of; lia.
  rewrite /nat_of; nia.
Qed.

(* The words of B_p, p <> j, are outside those of B_j. *)
Lemma coef_disjoint (j p L q : nat) : p <> j ->
  (p * L <= q)%coq_nat -> (q < p * L + L)%coq_nat ->
  (q < j * L \/ j * L + L <= q)%coq_nat.
Proof. move=> H H1 H2; nia. Qed.

(* The k coefficients become their forward differences at 0, modulo
   beta^l; the words after them are unchanged. *)
Theorem difftab_spec xs m k l e1 result :
  let K := nat_of k in let L := nat_of l in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat ->
  eval_funcall ge (Internal difftab29)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l] e1 (Some result) ->
  exists xs', e1!(param 0 difftab29) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    vcoefs xs' L K =
      map (fun j => fdiff (vcoefs xs L K) j mod base L)%Z (seq 0 K) /\
    skipn (K * L) xs' = skipn (K * L) xs.
Proof.
  move=> K L Hlen HKL.
  intro_eval_funcall difftab29 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "j" J.
  name_var "B" A.
  repeat prog.
  pose X := vcoef xs L.
  (* Before pass i: B_p holds the difference of order min p (i-1). *)
  pose Inv := fun (e: env) (se: senv) =>
    exists ii xs', e!i = Some (Vint64 ii) /\ (1 <= Int64.unsigned ii)%Z /\
      e!A = Some (Varr (map Vint64 xs')) /\ length xs' = length xs /\
      skipn (K * L) xs' = skipn (K * L) xs /\
      forall p, (p < K)%coq_nat ->
        vcoef xs' L p = (stage X (nat_of ii - 1) p mod base L)%Z.
  exists Inv; split.
  - exists (Int64.repr 1), xs; repeat split => //.
    move=> p Hp; rewrite /stage.
    have -> : Nat.min p (nat_of (Int64.repr 1) - 1) = 0%nat by
      rewrite /nat_of; clia.
    rewrite Nat.sub_0_r [dif _ _ _]/= /X Z.mod_small //; apply: vcoef_bound.
  - move=>>.
    repeat prog.
    rewrite /Inv /=.
    intros (ii & xs' & [= ->] & Hi1 & [= ->] & Hl & Hsk & HV) => /=.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      set a := (nat_of ii - 1)%nat.
      have Ha : nat_of ii = a.+1 by rewrite /a /nat_of; clia ii.
      have HiK : (nat_of ii < K)%coq_nat by rewrite /K /nat_of; clia ii, k.
      (* Pass i, down to j: B_p, p > j, holds the difference of order
         min p i. *)
      pose Inv2 := fun (e: env) (se: senv) =>
        exists jj ys, e!J = Some (Vint64 jj) /\
          (Int64.unsigned jj < Int64.unsigned k)%Z /\
          (Int64.unsigned ii <= Int64.unsigned jj + 1)%Z /\
          e!A = Some (Varr (map Vint64 ys)) /\ length ys = length xs /\
          skipn (K * L) ys = skipn (K * L) xs /\
          forall p, (p < K)%coq_nat ->
            vcoef ys L p =
              ((if Nat.ltb (nat_of jj) p then stage X a.+1 p else stage X a p)
                 mod base L)%Z.
      exists Inv2; split.
      * exists (Int64.sub k (Int64.repr 1)), xs'; repeat split => //.
        -- clia ii, k.
        -- clia ii, k.
        -- move=> p Hp; rewrite HV //.
           have -> : Nat.ltb (nat_of (Int64.sub k (Int64.repr 1))) p = false.
           { apply/Nat.ltb_ge; rewrite /K /nat_of in Hp *; clia k. }
           done.
      * move=>>.
        repeat prog.
        rewrite /Inv2 /=.
        intros (jj & ys & [= ->] & Hjk & Hij & [= ->] & Hyl & Hysk & HW) => /=.
        simplWP.
        case END2: (Int64.ltu jj ii); simplWP.
        2: {
        repeat prog.
        move=> _ _; rewrite /sem_binarith /sem_cast /=; move=> CALL.
        have Hj1 : (Int64.unsigned ii <= Int64.unsigned jj)%Z.
        { by move: END2; rewrite /Int64.ltu; case: zlt => //; lia. }
        have [E1 [E2 E3]] := idx_facts jj k l m ltac:(lia) Hjk HKL.
        move/subw_spec: CALL; cbv zeta => CALL.
        have [ys' [Ey [Hly [Hval Hout]]]] := CALL
          ltac:(by rewrite Hyl) ltac:(lia) ltac:(lia) ltac:(lia).
        repeat prog.
        set JJ := nat_of jj.
        have HJK : (JJ < K)%coq_nat by rewrite /JJ /K /nat_of; lia.
        have HJa : (a < JJ)%coq_nat by rewrite /JJ /nat_of in Ha *; lia.
        have Hsub : nat_of (Int64.sub jj (Int64.repr 1)) = JJ.-1.
        { rewrite /JJ /nat_of; clia jj, ii. }
        have EJ : (JJ * L)%nat = nat_of (Int64.mul jj l) by rewrite E1; lia.
        have EJ1 :
          (JJ.-1 * L)%nat = nat_of (Int64.mul (Int64.sub jj (Int64.repr 1)) l).
        { have HJ1 : (1 <= JJ)%coq_nat by lia.
          rewrite -EJ in E2; clear -E2 HJ1; nia. }
        exists (Int64.sub jj (Int64.repr 1)), ys'.
        have PA : param 0 subw19 = A by [].
        rewrite PA in Ey; rewrite Ey /=.
        repeat split => //.
        -- clia jj, k, ii.
        -- clia jj, ii.
        -- by rewrite Hly.
        -- rewrite -Hysk; apply: skipn_eq_nth; first lia.
           move=> q Hq; apply: Hout; right; rewrite -/L; lia.
        -- move=> p Hp; rewrite Hsub.
           case: (Nat.eq_dec p JJ) => [->|Hne].
           ++ have -> : Nat.ltb JJ.-1 JJ = true by apply/Nat.ltb_lt; lia.
              rewrite /vcoef /coef EJ -/L Hval -EJ1 -EJ.
              rewrite -/(coef ys L JJ) -/(coef ys L JJ.-1).
              rewrite -/(vcoef ys L JJ) -/(vcoef ys L JJ.-1).
              have HJ1K : (JJ.-1 < K)%coq_nat by lia.
              rewrite (HW _ HJK) (HW _ HJ1K).
              have -> : Nat.ltb JJ JJ = false by apply/Nat.ltb_ge; lia.
              have -> : Nat.ltb JJ JJ.-1 = false by apply/Nat.ltb_ge; lia.
              by rewrite -Zminus_mod stage_step.
           ++ rewrite /vcoef (coef_eq_nth ys' ys); first by rewrite Hly.
              { move=> q H1 H2; apply: Hout; rewrite -/L -EJ.
                exact: (coef_disjoint _ _ _ _ Hne H1 H2). }
              rewrite -/(vcoef ys L p) HW //.
              have -> : Nat.ltb JJ.-1 p = Nat.ltb JJ p.
              { case: Nat.ltb_spec; case: Nat.ltb_spec => //; lia. }
              done. }
        (* The pass ends at j = i - 1. *)
        simplWP.
        repeat prog.
        have Hik : (Int64.unsigned ii < Int64.unsigned k)%Z.
        { by move: END; rewrite /Int64.ltu; case: zlt. }
        have Hja : nat_of jj = a.
        { move: END2; rewrite /Int64.ltu; case: zlt => // H _.
          rewrite /a /nat_of; lia. }
        have Hadd : nat_of (Int64.add ii (Int64.repr 1)) = (nat_of ii).+1.
        { rewrite /nat_of; clia ii, k. }
        exists (Int64.add ii (Int64.repr 1)), ys.
        rewrite /sem_binarith /sem_cast /=.
        split; first done.
        split; first by clia ii, k.
        split; first done.
        split; first done.
        split; first done.
        move=> p Hp; rewrite Hadd Ha.
        have -> : (a.+2 - 1)%nat = a.+1 by lia.
        rewrite (HW _ Hp) Hja.
        case: Nat.ltb_spec => H //.
        by rewrite stage_low.
    (* The last pass is done: B_p is the difference of order p. *)
    + have HKi : (K <= nat_of ii)%coq_nat.
      { move: END; rewrite /Int64.ltu /K /nat_of; case: zlt => // H _; lia. }
      exists xs'.
      split; first done.
      split; first done.
      split; last done.
      rewrite /vcoefs; apply: map_ext_in => p; rewrite in_seq => Hp.
      rewrite (HV p); first lia.
      rewrite stage_end; first lia.
      by rewrite fdiff_dif; first lia.
Qed.
