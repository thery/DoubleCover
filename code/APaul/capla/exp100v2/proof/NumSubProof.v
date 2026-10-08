(** * num_sub: a = a - b, for a >= b

    The loop invariant is the one of the VST proof (body_num_sub of
    ../../../vst/exp100/Verif_simple.v): after i rounds, the i low limbs
    of a minus the borrow c at weight 2^(32 i) stand for the difference
    of the i low limbs of a and b, the limbs from i on are those of a,
    and the borrow is 0 or 1. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import Exp100Capla2.LimbLemmas.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Section Lemmas.
Local Open Scope Z_scope.

(* One round of the borrow loop on the numbers. *)
Lemma sub_step (P A Bb B c x y v c' : Z) :
  P - c * B = A - Bb -> v - c' * 2 ^ 32 = x - y - c ->
  (P + B * v) - c' * (2 ^ 32 * B) = (A + B * x) - (Bb + B * y).
Proof.
  move=> HV Ev.
  have -> : v = x - y - c + c' * 2 ^ 32 by lia.
  nia.
Qed.

Context {n : nat}.
Implicit Types a : {ffun 'I_n -> int64}.

End Lemmas.

Theorem num_sub_ok : num_sub_spec.
Proof.
  move=> μ a0 b0 r rl La Lb Hs.
  start. csteps.
  inv I := { [:: a; c; i; _i_hi] } (fun (a : numA) (c i hi : int64) =>
    Int64.unsigned hi = 6 /\ Int64.unsigned i <= 6 /\
    Int64.unsigned c <= 1 /\
    (forall j : 'I_NL, (Z.to_nat (Int64.unsigned i) <= j)%nat -> a j = a0 j) /\
    (forall j : 'I_NL, (j < Z.to_nat (Int64.unsigned i))%nat ->
       limb (Int64.unsigned (a j))) /\
    pval a (Z.to_nat (Int64.unsigned i)) -
      Int64.unsigned c * limb_base (Z.to_nat (Int64.unsigned i)) =
    pval a0 (Z.to_nat (Int64.unsigned i)) -
      pval b0 (Z.to_nat (Int64.unsigned i))).
  enter_loop I.
  { prove_inv; exsp.
    change (Int64.repr 0) with Int64.zero; rewrite Int64.unsigned_zero.
    rewrite (_ : Z.to_nat 0 = 0%nat) //.
    rewrite !pval0; lia. }
  unfold_inv => - [Hhi [Hi [Hc [Hhigh [Hlow HV]]]]].
  csteps.
  case END: Int64.ltu => /=.
  - (* one round: limb i of the difference, and the borrow *)
    have Hk : (i0:N < 6)%nat by clia i0.
    have Ek : (Int64.add i0 (Int64.repr 1)):N = (i0:N).+1 by clia i0.
    pose o : 'I_NL := @Ordinal NL (i0:N) Hk.
    have Eo : forall p, @Ordinal NL (i0:N) p = o by move=> p; apply: val_inj.
    have Eo' : forall p, @Ordinal ((Int64.repr 6):N) (i0:N) p = o.
      by move=> p; apply: val_inj.
    have Hx : a1 o = a0 o by apply: Hhigh; rewrite /= leqnn.
    have Lx := La o; have Ly := Lb o.
    move: Lx Ly; rewrite /limb /limb_bits -Hx => Lx Ly.
    have Et := add2_unsigned (b0 o) c0 ltac:(lia) Hc.
    (* the limbs above o are those of a0, the limbs below are limbs *)
    have Hup : forall v, forall j : 'I_NL,
        ((Int64.add i0 (Int64.repr 1)):N <= j)%nat ->
        [ffun i1 : 'I_NL => if i1 == o then v else a1 i1] j = a0 j.
    { move=> v j; rewrite Ek ffunE => Hj; case: eqP => [Ej|_].
      - by move: Hj; rewrite Ej ltnn.
      - by apply: Hhigh; apply: ltnW. }
    have Hlo : forall v, limb (Int64.unsigned v) -> forall j : 'I_NL,
        (j < (Int64.add i0 (Int64.repr 1)):N)%nat ->
        limb (Int64.unsigned
                ([ffun i1 : 'I_NL => if i1 == o then v else a1 i1] j)).
    { move=> v Lv j; rewrite Ek ffunE ltnS leq_eqVlt => /orP [/eqP Ej|Hj].
      - have -> : j = o by apply: val_inj.
        by rewrite eqxx.
      - case: eqP => [Ej'|_]; first by move: Hj; rewrite Ej' ltnn.
        by apply: Hlow. }
    have Hval : forall w c1,
        Int64.unsigned w - Int64.unsigned c1 * 2 ^ 32 =
          Int64.unsigned (a1 o) - Int64.unsigned (b0 o) - Int64.unsigned c0 ->
        pval [ffun i1 : 'I_NL => if i1 == o then w else a1 i1]
          (Int64.add i0 (Int64.repr 1)):N -
        Int64.unsigned c1 * limb_base (Int64.add i0 (Int64.repr 1)):N =
        pval a0 (Int64.add i0 (Int64.repr 1)):N -
        pval b0 (Int64.add i0 (Int64.repr 1)):N.
    { move=> w c1 Ev.
      rewrite Ek -[(i0:N).+1]/(nat_of_ord o).+1 pval_upd.
      rewrite limb_baseS (pvalS a0 o) (pvalS b0 o) -Hx /limb_bits.
      by apply: (sub_step (pval a1 o) (pval a0 o) (pval b0 o) (limb_base o)
                (Int64.unsigned c0)). }
    csteps; evalf; csteps; evalf; csteps.
    case LT: Int64.ltu => /=.
    + (* a[i] < b[i] + c: borrow *)
      csteps; evalf; csteps; evalf; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      move: LT; rewrite ?Eo ?Eo' /Int64.ltu; case: Coqlib.zlt => // HLT _.
      have Ev := borrow_unsigned (a1 o) (Int64.add (b0 o) c0)
                   ltac:(rewrite Et; lia).
      prove_inv; rewrite ?Eo ?Eo'; exsp.
      { clia i0. }
      { exact: Hup. }
      { by apply: Hlo; rewrite /limb /limb_bits Ev Et; lia. }
      by apply: Hval; rewrite Ev Et; change (Int64.unsigned (Int64.repr 1)) with 1; lia.
    + (* b[i] + c <= a[i]: no borrow *)
      csteps; evalf; csteps; evalf; csteps.
      cret; split=> // _; split.
      { solve_loop_conditions. }
      move: LT; rewrite ?Eo ?Eo' /Int64.ltu; case: Coqlib.zlt => // HGE _.
      have Ev := sub_unsigned (a1 o) (Int64.add (b0 o) c0) ltac:(lia).
      prove_inv; rewrite ?Eo ?Eo'; exsp.
      { clia i0. }
      { exact: Hup. }
      { by apply: Hlo; rewrite /limb /limb_bits Ev Et; lia. }
      by apply: Hval; rewrite Ev Et; change (Int64.unsigned (Int64.repr 0)) with 0; lia.
  - (* the loop ends with i = 6: the borrow is 0 *)
    csteps; cret; split=> //= _; csteps; fin.
    have E6 : i0:N = 6%nat by clia i0.
    have L1 : limbsA a1.
    { move=> j; apply: Hlow; rewrite E6; exact: ltn_ord j. }
    exists a1; split; first by rewrite/envC/=.
    split => //.
    have P1 : pval a1 NL = valA a1 := pval_all a1.
    have Pa : pval a0 NL = valA a0 := pval_all a0.
    have Pb : pval b0 NL = valA b0 := pval_all b0.
    have B1 : 0 <= valA a1 < limb_base NL := @valA_bound NL a1 L1.
    move: HV; rewrite E6.
    change (pval a1 NL - Int64.unsigned c0 * limb_base NL =
            pval a0 NL - pval b0 NL -> valA a1 = valA a0 - valA b0).
    rewrite P1 Pa Pb => HV.
    have [E0|E1] : Int64.unsigned c0 = 0 \/ Int64.unsigned c0 = 1.
    { have := Int64.unsigned_range c0; lia. }
    { by move: HV; rewrite E0; lia. }
    by move: HV; rewrite E1; lia.
Qed.
