(** * num_copy: a = b

    The loop invariant is the one of the VST proof (body_num_copy of
    ../../../vst/exp100/Verif_simple.v): after i rounds, the i low words
    of a are those of b. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

Theorem num_copy_ok : num_copy_spec.
Proof.
move=> μ a0 b0 r rl.
start; csteps.
(* the i low words of a are those of b *)
inv I := { [:: a; i] } (fun (a : numA) (i : int64) =>
  (i:N <= NL)%nat /\ forall j : 'I_NL, (j < i:N)%nat -> a j = b0 j).
enter_loop I.
{ prove_inv; exsp. }
unfold_inv => - [Hi Ha].
csteps.
case LT: Int64.ltu => /=.
- csteps; rewrite (fffE' _ _ H) /= setf_map.
  cret; split=> // _; split.
  { solve_loop_conditions. }
  prove_inv; exsp.
  { clia i0. }
  move=> j Hj; evalf.
  case: eqP => [->|ne]; first by congr (b0 _); apply: val_inj.
  apply: Ha; have: (nat_of_ord j) <> (i0:N).
  { by move=> E; apply: ne; apply: val_inj. }
  clia i0.
- csteps; cret; split=> //= _; csteps; fin.
  rewrite/envC/=; do 2 f_equal; apply/ffunP => x; rewrite !ffunE.
  have Ei : (i0:N = 6)%nat by move: Hi; rewrite /NL; clia i0.
  congr Vint64; apply: Ha; rewrite Ei; exact: ltn_ord.
Qed.
