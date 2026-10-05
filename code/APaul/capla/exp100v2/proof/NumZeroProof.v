(** * num_zero: a = 0

    The loop invariant: after i rounds, the limbs below i are 0 and the
    others are those of a. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Theorem num_zero_ok : num_zero_spec.
Proof.
  move=> μ a0 r rl.
  enter_func. csteps.
  inv I := { [:: a; i; _i_hi] } (fun (a : numA) (i hi : int64) =>
    Int64.unsigned hi = 6 /\ Int64.unsigned i <= 6 /\
    a = [ffun j : 'I_NL =>
           if (j < Z.to_nat (Int64.unsigned i))%nat then Int64.zero
           else a0 j]).
  enter_loop I.
  { prove_inv; exsp.
    by apply/ffunP => j; rewrite ffunE. }
  unfold_inv => - [Hhi [Hi ->]].
  csteps.
  case END: Int64.ltu => /=.
  - (* one more limb set to 0 *)
    csteps; cret; split=> // _; split.
    { solve_loop_conditions. }
    prove_inv; exsp.
    { clia i0. }
    apply/ffunP => j; evalf.
    case: eqP => [Hj|Hj].
    + case: ifP => H1 //; exfalso.
      by move: H1; rewrite Hj /=; clia i0.
    + have Hj' : (j : nat) <> i0:N by move=> E; apply: Hj; apply: val_inj.
      by case: ifP => H1; case: ifP => H2 //; exfalso; clia i0.
  - (* the loop ends with i = 6: every limb is 0 *)
    csteps; cret; split=> //= _; csteps; cret.
    rewrite/envC/=; do 2 f_equal; apply/ffunP => j; evalf.
    case: ifP => // H1; exfalso.
    have Hj : (j < 6)%nat := ltn_ord j.
    have Hi6 : Int64.unsigned i0 = 6 by clia i0.
    by move: H1; rewrite Hi6 Hj.
Qed.
