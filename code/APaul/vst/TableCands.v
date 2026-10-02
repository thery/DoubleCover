(** * A line of the table: its hard inputs are candidates

    [line_ok] (code/exptablekl/ExpCheck.v) is what the table check
    establishes for one line.  Here, on such a line, every [j < n] whose
    input [(S0 + j) 2^(ex - 52)] is [hard] (code/exptablekl/ExpHard.v) is
    among the candidates [cands] of the table of the line, with the [k]
    and [l] of the line and the window [ERR]: [cands_line].  [cands] is
    that of code/APaul/rocq/HtrDefs.v, which [Spec_search.v] copies.  The
    pieces: [HtrMath.table_head] and [HtrMath.top_hit] (the table holds
    [P(j)], the test of [hscan] implies the top-word test) and
    [TaylorLink.hscan_exp] (the reals: [hscan] keeps [j]).  No VST here:
    mathcomp and VST are kept in separate files. *)

From Stdlib Require Import Reals Lra ZArith List Lia.
Import ListNotations.
From APaulRocq Require TaylorReal Shift TaylorScan TaylorLink HtrMath.
From APaulRocq Require Import HtrDefs.
From ExpTableKL Require ExpCheck ExpHard.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** [hscan_exp] over [Z] and [list Z]

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

Local Notation line_ok := ExpCheck.line_ok.
Local Notation hard := ExpHard.hard.
Local Notation bp := ExpCheck.bp.
Local Notation uexp := ExpCheck.uexp.
Local Notation ERR := ExpCheck.ERR.

(** ** The two descriptions of a line agree *)

(** The sums of [ExpCheck] and of [TaylorReal]. *)
Lemma sumR_TaylorReal (f : nat -> R) (N : nat) :
  TaylorReal.sumR N f = ExpCheck.sumR f N.
Proof. by elim: N => [|N IH] //=; rewrite IH. Qed.

(** The polynomials of [ExpCheck] and of [HtrDefs]. *)
Lemma Pz_polyZ k (A : list Z) j :
  length A = k -> ExpCheck.Pz k A j = polyZ A j.
Proof. by move=> hA; rewrite /ExpCheck.Pz /polyZ hA. Qed.

(** [beta^l] of [ExpCheck] is [baseZ l]. *)
Lemma beta_l_baseZ l : (0 <= l)%Z -> ExpCheck.beta_l l = baseZ l.
Proof.
move=> l0; rewrite /ExpCheck.beta_l /ExpCheck.beta /baseZ /wbits.
by rewrite -Z.pow_mul_r //; lia.
Qed.

(** The window [E l] of [ExpCheck] is [ERR beta^(l-1)]. *)
Lemma E_ERR l : (1 <= l)%Z ->
  ExpCheck.E l = (ERR * 2 ^ (wbits * (l - 1)))%Z.
Proof.
move=> l1; rewrite /ExpCheck.E /ExpCheck.beta /wbits.
by rewrite -Z.pow_mul_r //; lia.
Qed.

(** A natural number [j] as a real. *)
Lemma INR_Z2N (j : Z) : (0 <= j)%Z -> INR (Z.to_nat j) = IZR j.
Proof. by move=> j0; rewrite INR_IZR_INZ Z2Nat.id. Qed.

(** The [n] of a line fits in 53 bits. *)
Lemma line_ok_n S0 ex n k l B :
  line_ok S0 ex n k l B -> (1 <= n < 2 ^ 53)%Z.
Proof.
move=> hok; destruct hok as (e & hn & h52 & h53 & hsg & _).
change ExpCheck.drop with 1%Z in *.
have : (0 < S0 /\ 0 < S0 + n - 1 \/ S0 < 0 /\ S0 + n - 1 < 0)%Z by nia.
by lia.
Qed.

(** The [k] and [l] of a line: condition 6. *)
Lemma line_ok_kl S0 ex n k l B :
  line_ok S0 ex n k l B ->
  ((1 <= k)%coq_nat /\ (k <= 13)%coq_nat) /\ (1 <= l <= 8)%Z.
Proof.
move=> hok; destruct hok as (e & _ & _ & _ & _ & _ & _ & _ & _ & _ & hk &
  hl & _).
change ExpCheck.kmax with 13%nat in hk.
by change ExpCheck.lmax with 8%Z in hl; lia.
Qed.

(** The values [B] of a line have [k] elements. *)
Lemma line_ok_B S0 ex n k l B : line_ok S0 ex n k l B -> length B = k.
Proof.
by move=> hok; destruct hok as (e & _ & _ & _ & _ & _ & _ & (A & _ & hB & _)
  & _).
Qed.

(** ** The theorem *)

Theorem cands_line S0 ex n k l B :
  line_ok S0 ex n k l B ->
  forall j, (0 <= j < n)%Z ->
  hard (IZR (S0 + j) * bp (uexp ex)) ->
  In (Z.to_nat j) (cands l ERR B (Z.to_nat n)).
Proof.
move=> hok j hj hhard.
have [n1 n53] := line_ok_n S0 ex n k l B hok.
have [[k1 k13] [l1 l8]] := line_ok_kl S0 ex n k l B hok.
move: hok; rewrite /ExpCheck.line_ok; cbv zeta.
change ExpCheck.drop with 1%Z.
move=> hok.
destruct hok as (e & _ & _ & _ & _ & hv0 & hvl & (A & hlA & hlB & hA & hB) &
  hT & hE & _ & _ & hEl).
set u := bp (uexp ex) in hv0 hvl hA hT hE hhard *.
set v := ExpCheck.bp (ExpCheck.vexp e) in hA hT hE *.
set rho := (exp _ * _ / _)%R in hT hE.
have u0 : (0 < u)%R by apply: Flocq.Core.Raux.bpow_gt_0.
(* x = x0 + j u, and v = vof x *)
have hx : (IZR (S0 + j) * u = IZR S0 * u + IZR j * u)%R.
  by rewrite plus_IZR; ring.
have hvx : ExpHard.vof (IZR (S0 + j) * u) = v.
  apply: (ExpHard.vof_line e _ _ _ hv0 hvl).
  rewrite hx; split.
    have : (0 <= IZR j)%R by apply: IZR_le; lia.
    by move=> hj0; nra.
  have : (IZR j <= IZR (n - 1))%R by apply: IZR_le; lia.
  have -> : (S0 + n - 1 = S0 + (n - 1))%Z by lia.
  by rewrite (plus_IZR S0 (n - 1)) => hjn; nra.
move: hhard; rewrite /ExpHard.hard hvx hx => hz.
(* the hypotheses of hit_polyZ, from the conditions of the line *)
have hbl := beta_l_baseZ l ltac:(lia).
have M0 : (0 < baseZ l)%Z.
  by rewrite /baseZ /wbits; apply: Z.pow_pos_nonneg; lia.
have EM : (2 * ExpCheck.E l < baseZ l)%Z by rewrite -hbl.
have hA' : forall i, (i < length A)%coq_nat ->
    (Rabs (IZR (nth i A 0%Z) - IZR (baseZ l) *
             frac_part (ExpCheck.a (IZR S0 * u) u i / v)) < 1)%R.
  move=> i hi; have [_] := hA i ltac:(lia).
  by rewrite ExpHard.fracR_frac_part hbl.
have hj0 : (0 <= j)%Z by lia.
have hT' := hT j ltac:(lia).
rewrite -sumR_TaylorReal -(INR_Z2N j hj0) in hT'.
rewrite [in exp _](INR_Z2N j hj0) -hlA in hT'.
have nR : INR (Z.to_nat n) = IZR n by apply: INR_Z2N; lia.
rewrite hbl -sumR_TaylorReal -nR -hlA in hE.
have jN : (Z.to_nat j < Z.to_nat n)%N by apply/ltP; lia.
have hhit := Reals_Z.hit_polyZ A (baseZ l) (ExpCheck.E l) (Z.to_nat n)
  (Z.to_nat j) (fun i => ExpCheck.a (IZR S0 * u) u i / v)%R rho
  (bp (- ExpCheck.m)) (exp (IZR S0 * u + IZR j * u) / v)%R M0 EM jN hA'
  hT' hE hz.
rewrite E_ERR // in hhit.
(* B holds P(0) .. P(k-1) modulo beta^l *)
have hBe : B =
    map (fun i => polyZ A (Z.of_nat i) mod baseZ l)%Z (seq 0 (length A)).
  apply: (nth_ext _ _ 0%Z 0%Z).
    by rewrite length_map length_seq hlB.
  move=> i hi; rewrite hlB in hi.
  rewrite hB //.
  rewrite (nth_indep _ 0%Z (polyZ A (Z.of_nat 0) mod baseZ l)%Z).
    by rewrite length_map length_seq hlA.
  by rewrite map_nth seq_nth ?hlA // (Pz_polyZ k) // hbl.
(* so j is a candidate *)
rewrite /cands; apply/filter_In; split; first by apply/in_seq; lia.
rewrite /cand hBe; apply/Z.leb_le.
have := @HtrMath.table_head A l ERR (Z.to_nat j)
  (ltac:(apply/ltP; lia)) l1.
have := @HtrMath.top_hit l ERR (polyZ A (Z.of_nat (Z.to_nat j))) l1
  ltac:(rewrite /ERR; lia).
rewrite /top => Ht Hh.
by rewrite Hh; apply: Ht; exact: hhit.
Qed.
