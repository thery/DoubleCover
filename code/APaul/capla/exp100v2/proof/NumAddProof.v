(** * num_add: a = a + b, when the sum fits

    The loop invariant is the one of the VST proof (body_num_add of
    ../../../vst/exp100/Verif_simple.v): after i rounds, the i low limbs
    of a and the carry c stand for the sum of the i low limbs of a and b,
    the limbs from i on are those of a, and the carry is 0 or 1. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Section Lemmas.
Local Open Scope Z_scope.

(* One round of the carry loop on the numbers. *)
Lemma add_step (P A Bb B c x y s : Z) :
  0 <= c <= 1 -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 < B ->
  s = c + x + y -> P + c * B = A + Bb ->
  (P + B * (s mod 2 ^ 32)) + s / 2 ^ 32 * (2 ^ 32 * B) =
  (A + B * x) + (Bb + B * y).
Proof.
  move=> Hc Hx Hy HB Es HV.
  have E := Z.div_mod s (2 ^ 32) ltac:(lia).
  nia.
Qed.

(* The carry out of one round is 0 or 1. *)
Lemma add_carry (c x y : Z) :
  0 <= c <= 1 -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (c + x + y) / 2 ^ 32 <= 1.
Proof.
  move=> Hc Hx Hy.
  have H : c + x + y < 2 ^ 32 * 2 by lia.
  have := Z.div_lt_upper_bound (c + x + y) (2 ^ 32) 2 ltac:(lia) H; lia.
Qed.

Context {n : nat}.
Implicit Types a : {ffun 'I_n -> int64}.

End Lemmas.

Theorem num_add_ok : num_add_spec.
Proof.
  move=> μ a0 b0 r rl La Lb Hs.
  enter_func. csteps.
  inv I := { [:: a; c; i; _i_hi] } (fun (a : numA) (c i hi : int64) =>
    Int64.unsigned hi = 6 /\ Int64.unsigned i <= 6 /\
    Int64.unsigned c <= 1 /\
    (forall j : 'I_NL, (Z.to_nat (Int64.unsigned i) <= j)%nat -> a j = a0 j) /\
    (forall j : 'I_NL, (j < Z.to_nat (Int64.unsigned i))%nat ->
       limb (Int64.unsigned (a j))) /\
    pval a (Z.to_nat (Int64.unsigned i)) +
      Int64.unsigned c * limb_base (Z.to_nat (Int64.unsigned i)) =
    pval a0 (Z.to_nat (Int64.unsigned i)) +
      pval b0 (Z.to_nat (Int64.unsigned i))).
  enter_loop I.
  { prove_inv; exsp.
    change (Int64.repr 0) with Int64.zero; rewrite Int64.unsigned_zero.
    rewrite (_ : Z.to_nat 0 = 0%nat) //.
    rewrite !pval0; lia. }
  unfold_inv => - [Hhi [Hi [Hc [Hhigh [Hlow HV]]]]].
  csteps.
  case END: Int64.ltu => /=.
  - (* one round: limb i of the sum, and the carry *)
    csteps; evalf; csteps; evalf; csteps.
    cret; split=> // _; split.
    { solve_loop_conditions. }
    have Hk : (i0:N < 6)%nat by clia i0.
    have Ek : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1 by clia i0.
    set o := (i0:N):'I_NL.
    have Eo : forall p, @Ordinal NL (i0:N) p = o by move=> p; apply: val_inj.
    have Eo' : forall p, @Ordinal ((Int64.repr 6):N) (i0:N) p = o.
      by move=> p; apply: val_inj.
    have Hx : a1 o = a0 o by apply: Hhigh; rewrite /= leqnn.
    have Lx := La o; have Ly := Lb o.
    move: Lx Ly; rewrite /limb /limb_bits -Hx => Lx Ly.
    have Es := add3_unsigned c0 (a1 o) (b0 o) Hc ltac:(lia) ltac:(lia).
    prove_inv; rewrite ?Eo ?Eo'; exsp.
    set s := Int64.add (Int64.add c0 (a1 o)) (b0 o) in Es *.
    { clia i0. }
    { rewrite shru32 Es; apply: add_carry; lia. }
    { move=> j; rewrite Ek => Hj; rewrite setf_other.
      { by move=> E; move: Hj; rewrite E ltnn. }
      by apply: Hhigh; apply: ltnW. }
    { move=> j; rewrite Ek ltnS leq_eqVlt => /orP [/eqP Ej|Hj].
      - have -> : j = Ordinal Hk by apply: val_inj.
        rewrite setf_at and_mask /limb /limb_bits.
        apply: Z.mod_pos_bound; lia.
      - rewrite setf_other; first by move=> E; move: Hj; rewrite E ltnn.
        by apply: Hlow. }
    rewrite Ek pval_setf_top // and_mask shru32 limb_baseS.
    rewrite (pvalS a0 o) (pvalS b0 o) -Hx.
    rewrite /limb_bits.
    apply: (add_step (pval a1 (i0:N)) (pval a0 (i0:N)) (pval b0 (i0:N))
              (limb_base (i0:N)) (Int64.unsigned c0) (Int64.unsigned (a1 o))
              (Int64.unsigned (b0 o))) => //; try lia.
    exact: limb_base_pos.
  - (* the loop ends with i = 6: the carry is 0 *)
    csteps; cret; split=> //= _; csteps; cret.
    have E6 : i0:N = 6%nat by clia i0.
    exists a1; split; first by rewrite/envC/=.
    split.
    { move=> j; apply: Hlow; rewrite E6; exact: ltn_ord j. }
    have P1 : pval a1 NL = valA a1 := pval_all a1.
    have Pa : pval a0 NL = valA a0 := pval_all a0.
    have Pb : pval b0 NL = valA b0 := pval_all b0.
    have EB : limb_base NL = 2 ^ ExpModel.num_bits by [].
    have G := valA_ge0 a1.
    move: HV; rewrite E6.
    change (pval a1 NL + Int64.unsigned c0 * limb_base NL =
            pval a0 NL + pval b0 NL -> valA a1 = valA a0 + valA b0).
    rewrite P1 Pa Pb EB => HV.
    have [E0|E1] : Int64.unsigned c0 = 0 \/ Int64.unsigned c0 = 1.
    { have := Int64.unsigned_range c0; lia. }
    { by move: HV; rewrite E0; lia. }
    by move: HV; rewrite E1; lia.
Qed.
