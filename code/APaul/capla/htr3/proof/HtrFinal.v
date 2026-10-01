(** * T8: the Capla search misses no hard-to-round input

    On one line of the table, every [j < n] whose [y = exp(x0 + j u) / v]
    is within [eps = 2^-m] of an integer is among the candidates written
    by the Capla [search] of [htr3.b], provided their number fits in the
    output array.  The pieces: [search_spec] (what the program computes),
    [HtrMath.table_head] and [HtrMath.top_hit] (the table holds [P(j)],
    the test of [hscan] implies the top-word test), and
    [TaylorLink.hscan_exp] (the reals: [hscan] keeps [j]). *)

From Stdlib Require Import Reals Lra.
From APaulRocq Require TaylorReal Shift TaylorScan TaylorLink HtrMath.

From Stdlib Require Import BinNums ZArith List Lia Utf8.
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
Require Import Htr3.SearchProof.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** The reals, over [Z] and [list Z]

    [hscan_exp] is stated on mathcomp's [int] and [seq]; here it is
    restated on [Z] and [list Z], as the test of [hscan] on [polyZ A j].
    The mathcomp algebra is imported in this module only. *)

Module Reals_Z.

From mathcomp Require Import all_ssreflect all_algebra.
Import TaylorReal Shift TaylorScan TaylorLink.
(* zify reads [%%] of [int] as [mod] (otherwise as [modZ]). *)
Import zify_ssreflect.SsreflectZifyInstances.

Lemma foldZ_acc (s : list Z) (x : Z) :
  List.fold_right Z.add x s = Z.add (List.fold_right Z.add Z0 s) x.
Proof. by elim: s => [|b s IH] /=; [|rewrite IH]; lia. Qed.

(** [polyZ] of HtrDefs is [Pz] of TaylorReal. *)
Lemma polyZ_Pz (A : list Z) j :
  polyZ A (Z.of_nat j) = Pz (fun i => List.nth i A Z0) (length A) j.
Proof.
rewrite /polyZ; elim: (length A) => [//|k IH].
by rewrite List.seq_S List.map_app List.fold_right_app /= foldZ_acc IH /=; lia.
Qed.

Lemma nth_int_of_Z (A : list Z) i :
  Z_of_int (nth 0%R (List.map int_of_Z A) i) = List.nth i A Z0.
Proof. by elim: A i => [|x A IH] [|i] //=; rewrite int_of_ZK. Qed.

Lemma Pz_ext (f g : nat -> Z) k j :
  (forall i, f i = g i) -> Pz f k j = Pz g k j.
Proof. by move=> fg; elim: k => [|k IH] //=; rewrite IH fg. Qed.

(** [hscan_exp] on [Z]: [P(j) + E] is at most [2 E] modulo [M]. *)
Lemma hit_polyZ (A : list Z) (M E : Z) (N j : nat) (a : nat -> R)
    (rho eps y : R) :
  Z.lt 0 M -> Z.lt (Z.mul 2 E) M -> (j < N)%N ->
  (forall i, Peano.lt i (length A) ->
     Rlt (Rabs (Rminus (IZR (List.nth i A Z0))
                       (Rmult (IZR M) (frac_part (a i))))) 1) ->
  Rle (Rabs (Rminus y (sumR (length A)
                             (fun i => Rmult (a i) (pow (INR j) i))))) rho ->
  Rle (Rplus (Rmult (IZR M) (Rplus eps rho))
             (sumR (length A) (fun i => pow (INR N) i))) (IZR E) ->
  (exists z : Z, Rlt (Rabs (Rminus y (IZR z))) eps) ->
  Z.le (Z.modulo (Z.add (polyZ A (Z.of_nat j)) E) M) (Z.mul 2 E).
Proof.
move=> M0 EM jN HA HT HE Hz.
have sA : size (List.map int_of_Z A) = length A.
  by rewrite size_map; elim: A {HA HT HE} => //= x A ->.
have := @hscan_exp (List.map int_of_Z A) (int_of_Z M) (int_of_Z E) N j a
  rho eps y.
rewrite !int_of_ZK sA => /(_ M0 EM jN) H.
have {}H := H _ HT HE Hz.
have /H : forall i, Peano.lt i (length A) ->
  Rlt (Rabs (Rminus (IZR (Z_of_int (nth 0%R (List.map int_of_Z A) i)))
     (Rmult (IZR M) (frac_part (a i))))) 1.
  by move=> i iA; rewrite nth_int_of_Z; apply: HA.
rewrite /hscan scanE mem_filter => /andP[hit _].
have := hpoly_Pz (List.map int_of_Z A) j.
rewrite sA (@Pz_ext _ (fun i => List.nth i A Z0) _ _ (nth_int_of_Z A)).
rewrite -polyZ_Pz.
move: hit; rewrite /TaylorScan.hit /P inE.
set h := hpoly _ _; clear -M0 EM => hit <-; zify.
have -> : Z.modulo (Z.add (Z_of_int h) E) M = r.
  by symmetry; apply: (Z.mod_unique _ _ q); lia.
lia.
Qed.

End Reals_Z.

(** ** The theorem

    The numbers of a line, in the notation of [doc/htr.md]: [K] Taylor
    coefficients [A_i] of [L] words, [M = beta^L], the window
    [E = err beta^(L-1)], [N] inputs [j = 0 .. N-1].  [a i] stands for
    [exp(x0) u^i / (i! v)], [y] for [exp(x0 + j u) / v].

    The link to [line_ok] of [code/exptable9/ExpCheck.v] (not imported:
    its Flocq is not Capla's) with [k = K], [l = L], [E = err beta^(l-1)]
    ([err = 0x600000], [l = 6]) and [closed = false] ([n = N]):
    - condition 3 gives [A], with [length A = K], (H_A) with
      [a i := a x0 u i / v] (its [fracR] and [frac_part] are both
      [r - floor r]), and [B_i = P(i) mod beta^l] (its [Pz] is [polyZ]):
      the array [xs] holds this [B] ([vcoefs] below);
    - condition 4 gives (H_T) for [j = 0 .. n-1], with the [rho] of the
      line;
    - condition 5 is (H_E), with [eps = 2^-m];
    - conditions 1 and 2 make [u] and [v] constant on the line, so that
      [x0 + j u] are the doubles of the line and [y] is the number whose
      distance to an integer says that [x0 + j u] is hard to round. *)
Theorem search_complete xs m k l n err outs cap e1 result
    (A : list Z) (a : nat -> R) (rho eps y : R) (j : nat) :
  let K := nat_of k in let L := nat_of l in let N := nat_of n in
  let M := base L in
  let E := (Int64.unsigned err * 2 ^ (64 * (Z.of_nat L - 1)))%Z in
  (* the arguments of search *)
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat ->
  (1 <= K)%coq_nat -> (1 <= L)%coq_nat ->
  (2 * Int64.unsigned err <= Int64.max_unsigned)%Z ->
  length outs = nat_of cap ->
  (* the array holds P(0) .. P(K-1) modulo M *)
  length A = K ->
  vcoefs xs L K = map (fun i => polyZ A (Z.of_nat i) mod M)%Z (seq 0 K) ->
  (* (H_A) *)
  (forall i, (i < K)%coq_nat ->
     Rlt (Rabs (Rminus (IZR (nth i A 0%Z))
                       (Rmult (IZR M) (frac_part (a i))))) 1) ->
  (* (H_T) *)
  Rle (Rabs (Rminus y
              (TaylorReal.sumR K (fun i => Rmult (a i) (pow (INR j) i)))))
      rho ->
  (* (H_E) *)
  Rle (Rplus (Rmult (IZR M) (Rplus eps rho))
             (TaylorReal.sumR K (fun i => pow (INR N) i)))
      (IZR E) ->
  (* the input j, hard to round *)
  (j < N)%coq_nat ->
  (exists z : Z, Rlt (Rabs (Rminus y (IZR z))) eps) ->
  (* the run of search *)
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l; Vint64 n;
     Vint64 err; Varr (map Vint64 outs); Vint64 cap] e1 (Some result) ->
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    ((nat_of c <= nat_of cap)%coq_nat ->
       In j (firstn (nat_of c) (map nat_of outs'))).
Proof.
move=> K L N M E Hxs HKL HK HL Herr Houts HlA Hv HA HT HE Hj Hz Hrun.
have [c [outs' [-> [He1 [Hc Hout]]]]] := search_spec xs m k l n err outs cap
  e1 result Hxs HKL HK HL Herr Houts Hrun.
exists c, outs'; split => //; split => // Hcap.
move: Hc Hout.
set cs := cands _ _ _ _ => Hc Hout.
have L1 : (1 <= Z.of_nat L)%Z by lia.
have err0 := Int64.unsigned_range err.
(* 2 E < M: err is below 2^63 *)
have P0 : (0 < 2 ^ (64 * (Z.of_nat L - 1)))%Z.
  by apply: Z.pow_pos_nonneg; lia.
have ME : M = (2 ^ 64 * 2 ^ (64 * (Z.of_nat L - 1)))%Z.
  by rewrite /M /base -Z.pow_add_r; [lia|lia|f_equal; lia].
have EM : (2 * E < M)%Z.
  rewrite ME /E; move: P0 Herr.
  change Int64.max_unsigned with (2 ^ 64 - 1)%Z.
  by generalize (2 ^ (64 * (Z.of_nat L - 1)))%Z (Int64.unsigned err); nia.
(* the test of hscan holds at j *)
have M0 : (0 < M)%Z by apply: base_pos.
have Hhit : (Z.modulo (Z.add (polyZ A (Z.of_nat j)) E) M <= 2 * E)%Z.
  apply: (Reals_Z.hit_polyZ A M E N j a rho eps y M0 EM (introT ltP Hj)
    _ _ _ Hz); by rewrite HlA.
(* so j is a candidate *)
have Hin : In j cs.
  rewrite /cs /cands; apply/filter_In; split; first by apply/in_seq; lia.
  rewrite Hv -HlA /cand; apply/Z.leb_le.
  have := @HtrMath.table_head A (Z.of_nat L) (Int64.unsigned err) j
    (ltac:(rewrite HlA; apply/ltP; lia)) L1.
  have := @HtrMath.top_hit (Z.of_nat L) (Int64.unsigned err)
    (polyZ A (Z.of_nat j)) L1 (proj1 err0).
  rewrite /top => Ht Hh.
  by rewrite Hh; apply: Ht; exact: Hhit.
(* and the first count entries of out are the candidates *)
have Hle : (length cs <= nat_of cap)%coq_nat.
  by move: Hcap; rewrite /nat_of Hc; lia.
have -> : nat_of c = length cs by rewrite /nat_of Hc; lia.
by move: Hout; rewrite Nat.min_l // (firstn_all2 cs) // => ->.
Qed.

(** ** The hypotheses can hold together

    All of them but the run of [search], on a line of one coefficient
    [P = 0] of one word, [err = 2], one input [j = 0] and [y = 0]. *)
Lemma search_complete_sat :
  let xs := [Int64.zero] in let one := Int64.one in let err := Int64.repr 2 in
  let K := nat_of one in let L := nat_of one in let N := nat_of one in
  let M := base L in
  let E := (Int64.unsigned err * 2 ^ (64 * (Z.of_nat L - 1)))%Z in
  let A := [0%Z] in let a := fun _ : nat => 0%R in
  let rho := 0%R in let eps := Rinv (IZR M) in let y := 0%R in
  let j := 0%nat in
  length xs = nat_of one /\ (K * L <= nat_of one)%coq_nat /\
  (1 <= K)%coq_nat /\ (1 <= L)%coq_nat /\
  (2 * Int64.unsigned err <= Int64.max_unsigned)%Z /\
  length A = K /\
  vcoefs xs L K = map (fun i => polyZ A (Z.of_nat i) mod M)%Z (seq 0 K) /\
  (forall i, (i < K)%coq_nat ->
     Rlt (Rabs (Rminus (IZR (nth i A 0%Z))
                       (Rmult (IZR M) (frac_part (a i))))) 1) /\
  Rle (Rabs (Rminus y
              (TaylorReal.sumR K (fun i => Rmult (a i) (pow (INR j) i)))))
      rho /\
  Rle (Rplus (Rmult (IZR M) (Rplus eps rho))
             (TaylorReal.sumR K (fun i => pow (INR N) i)))
      (IZR E) /\
  (j < N)%coq_nat /\
  (exists z : Z, Rlt (Rabs (Rminus y (IZR z))) eps).
Proof.
move=> xs one err K L N M E A a rho eps y j.
have n1 : nat_of one = 1%nat by [].
have M0 : (0 < IZR M)%R by apply: IZR_lt; apply: base_pos.
have eps0 : (0 < eps)%R by apply: Rinv_0_lt_compat.
have f0 : frac_part 0 = 0%R by exact: fp_R0.
rewrite /K /L /N n1.
split; first by [].
split; first by [].
split; first by [].
split; first by [].
split; first by [].
split; first by [].
split; first by [].
split.
  move=> i i1; have -> : i = 0%nat by lia.
  by rewrite /a f0 Rmult_0_r Rminus_0_r Rabs_R0; lra.
split.
  by rewrite /= /a /y /rho Rmult_0_l Rplus_0_l Rminus_0_r Rabs_R0; lra.
split.
  have Mi : Rmult (IZR M) (Rinv (IZR M)) = 1%R by field; lra.
  rewrite /eps /rho Rplus_0_r Mi; have -> : E = 2%Z by [].
  by simpl; lra.
split; first by lia.
by exists 0%Z; rewrite /y Rminus_0_r Rabs_R0.
Qed.
