(** * num_mul_small: p = a w on NP limbs, for a limb w

    The loop invariant is the one of the VST proof (body_num_mul_small of
    ../../../vst/exp100/Verif_simple.v): after i rounds, the i low limbs
    of p and the carry c stand for the i low limbs of a times w, and the
    carry is a limb. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** The steps *)

(* One round: c = a_i w + c; p_i = c mod 2^32; c = c / 2^32. *)
Lemma mul_small_step (P A c ai w : Z) k :
  (P + limb_base k * c = A * w)%Z ->
  let s := (ai * w + c)%Z in
  (P + limb_base k * (s mod 2 ^ 32) + limb_base k.+1 * (s / 2 ^ 32) =
   (A + limb_base k * ai) * w)%Z.
Proof.
  move=> HV s; rewrite limb_baseS /limb_bits.
  have Ed := Z.div_mod s (2 ^ 32) ltac:(lia).
  have E : (limb_base k * (s mod 2 ^ 32) + 2 ^ 32 * limb_base k * (s / 2 ^ 32) =
            limb_base k * s)%Z by rewrite {3}Ed; ring.
  rewrite -Z.add_assoc E /s.
  have -> : P = (A * w - limb_base k * c)%Z by lia.
  ring.
Qed.

(* The last write of a round, on the numbers. *)
Lemma step_close (P B B1 p m q A x x' w : Z) : x = x' ->
  (P + B * m + B1 * q = (A + B * x) * w)%Z ->
  (P + B * p + (m - p) * B + B1 * q = (A + B * x') * w)%Z.
Proof. move=> <- <-; ring. Qed.

Theorem num_mul_small_ok : num_mul_small_spec.
Proof.
  move=> μ p a w r rl Ha Hw.
  enter_func. csteps.
  inv I := { [:: p0; c; i] } (fun (pp : {ffun 'I_NP -> int64}) cc ii =>
    (ii:N <= 6)%nat /\
    (forall k : 'I_NP, (k < ii:N)%nat -> limb (Int64.unsigned (pp k))) /\
    limb (Int64.unsigned cc) /\
    (pval pp ii:N + limb_base ii:N * Int64.unsigned cc =
     pval a ii:N * Int64.unsigned w)%Z).
  enter_loop I.
  { prove_inv; exsp.
    all: try (change (Int64.repr 0):N with 0%nat; rewrite !pval0 Int64.unsigned_zero; lia).
    all: try (rewrite Int64.unsigned_zero /limb /limb_bits; lia).
    all: try done. }
  unfold_inv => - [Hi0 [Hp0 [Hc0 Hv0]]].
  csteps.
  case END: Int64.ltu => /=.
  - csteps; evalf; csteps.
    cret; split=> // _; split.
    { solve_loop_conditions. }
    prove_inv; exsp.
    all: have E1 : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1 by clia i0.
    all: have H' : (i0:N < NP)%nat by apply: ltn_trans H _.
    all: have La := Ha (Ordinal H).
    all: rewrite ?E1.
    all: set ai := a (Ordinal H).
    all: move: La Hw Hc0; rewrite /limb /limb_bits => La Hw' Hc'.
    all: have Es := mul_add_word ai w c0 ltac:(lia) ltac:(lia) ltac:(lia).
    all: set s := Int64.add (Int64.mul ai w) c0 in Es *.
    all: have Rs := Int64.unsigned_range s.
    + by [].
    + move=> k Hk; rewrite (setfP _ _ _ H').
      case: eqP => [_|Ne].
      * rewrite and_mask; have := Z.mod_pos_bound (Int64.unsigned s) (2 ^ 32); lia.
      * by apply: Hp0; lia.
    + rewrite shru32; split; first by apply: Z.div_pos; lia.
      apply: Z.div_lt_upper_bound; lia.
    + rewrite (pval_setf _ _ _ H') ?(pvalSn _ _ H') ?(pvalSn _ _ H) ?ltnSn; first by [].
      rewrite and_mask shru32.
      have := mul_small_step (pval p1 i0:N) (pval a i0:N) (Int64.unsigned c0)
                (Int64.unsigned ai) (Int64.unsigned w) i0:N Hv0.
      move=> E; cbv zeta in E; rewrite Es.
      apply: step_close E.
      by rewrite /ai; do 2 f_equal; apply: val_inj.
  - csteps; cret; split=> //= _; csteps.
    cret.
    have E6 : i0:N = 6%nat by clia i0.
    rewrite E6 in Hp0 Hv0.
    eexists; split.
    { by rewrite /envC /=. }
    change (Int64.repr 6):N with 6%nat.
    have H6 : (6 < NP)%nat by [].
    split.
    + move=> k; rewrite (setfP _ _ _ H6); case: eqP => [_|Ne].
      * by move: Hc0; rewrite /limb.
      * by apply: Hp0; move: (ltn_ord k) Ne; rewrite /NP; lia.
    + rewrite -[valA (p1 ↑[_ ← _])]pval_all -[valA a]pval_all.
      rewrite (pval_setf _ _ _ H6) // (pvalSn _ _ H6) ltnSn.
      move: Hv0; rewrite /NL; lia.
Qed.
