(** * Zimmermann's search (doc/htr.md): linking the reals to the scan

    [TaylorReal.real_lemma] ends on [Pz], a sum over [Z], and
    [TaylorScan.hscan_complete] starts on [hpoly], a Horner form over
    [int].  This file proves they are the same polynomial, and restates
    [hscan_complete] over [Z], in the shape [real_lemma] produces. *)

From Stdlib Require Import ZArith Reals Lia.
From APaulRocq Require Import TaylorReal.
From mathcomp Require Import all_ssreflect all_algebra ssrZ zify.
From APaulRocq Require Import Shift TaylorScan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** One more term of [Pz], without letting [/=] unfold the power. *)
Lemma PzE (f : nat -> Z) k j :
  Pz f k.+1 j =
  Z.add (Pz f k j) (Z.mul (f k) (Z.pow (Z.of_nat j) (Z.of_nat k))).
Proof. by []. Qed.

(** Peeling the constant term off [Pz]: the Horner step, over [Z]. *)
Lemma PzS (f : nat -> Z) k j :
  Pz f k.+1 j = Z.add (f O) (Z.mul (Z.of_nat j) (Pz (fun i => f i.+1) k j)).
Proof.
elim: k => [|k IH]; first by rewrite !PzE /=; lia.
by rewrite PzE IH PzE Nat2Z.inj_succ Z.pow_succ_r; lia.
Qed.

(** [hpoly] and [Pz] compute the same integer. *)
Lemma hpoly_Pz (A : seq int) (j : nat) :
  Z_of_int (hpoly A j) = Pz (fun i => Z_of_int (nth 0%R A i)) (size A) j.
Proof.
elim: A => [//|a A IH].
by rewrite [size _]/= PzS /= -IH; lia.
Qed.

(** [hscan_complete] over [Z], with the polynomial written as [Pz]. *)
Theorem hscan_completeZ (A : seq int) (M E : int) (n j : nat) (w : Z) :
  Z.lt (Z.mul 2 (Z_of_int E)) (Z_of_int M) -> (j < n)%N ->
  Z.le (Z.abs (Z.sub (Pz (fun i => Z_of_int (nth 0%R A i)) (size A) j)
                     (Z.mul (Z_of_int M) w)))
       (Z_of_int E) ->
  j \in hscan A M E n.
Proof.
rewrite -hpoly_Pz => EM jn Pw.
by apply: (@hscan_complete A M E n j (int_of_Z w) _ jn); rewrite /P; lia.
Qed.

(** The search misses nothing.  [y] stands for [exp(x0 + j u) / v], [a i]
    for the Taylor coefficient [exp(x0) u^i / (i! v)], [eps] for [2^-m].
    Under the three hypotheses of the note, (H_A) on the [A_i], (H_T) the
    Taylor bound [rho], and (H_E) on [E], if [y] is within [eps] of an
    integer then [j] is a candidate.  Real numbers are written with prefix
    functions ([Rle], [Rplus], ...), since mathcomp owns the infix ones. *)
Theorem hscan_exp (A : seq int) (M E : int) (n j : nat) (a : nat -> R)
    (rho eps y : R) :
  Z.lt 0 (Z_of_int M) -> Z.lt (Z.mul 2 (Z_of_int E)) (Z_of_int M) ->
  (j < n)%N ->
  (forall i, Peano.lt i (size A) ->
     Rlt (Rabs (Rminus (IZR (Z_of_int (nth 0%R A i)))
                       (Rmult (IZR (Z_of_int M)) (frac_part (a i))))) 1) ->
  Rle (Rabs (Rminus y (sumR (size A) (fun i => Rmult (a i) (pow (INR j) i)))))
      rho ->
  Rle (Rplus (Rmult (IZR (Z_of_int M)) (Rplus eps rho))
             (sumR (size A) (fun i => pow (INR n) i)))
      (IZR (Z_of_int E)) ->
  (exists z : Z, Rlt (Rabs (Rminus y (IZR z))) eps) ->
  j \in hscan A M E n.
Proof.
move=> M0 EM jn HA HT HE Hz.
have jn' : Peano.le j n by apply/leP; exact: ltnW.
have [w Hw] := real_lemma _ _ _ _ _ _ _ _ _ _ M0 jn' HA HT HE Hz.
exact: hscan_completeZ EM jn Hw.
Qed.
