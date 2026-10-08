(** * maybe_hard_bits: the filter maybe_hard_Z

    maybe_hard_bits calls exp_core and decide: their statements
    [exp_core_spec] and [decide_spec] are hypotheses of
    [maybe_hard_bits_ok], proved in ExpCoreProof.v and DecideProof.v.
    When exp_core fails, the result is 1; otherwise it is the decision
    on y and hs[0], whose bounds come from core_bounds. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.Tactics.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* rc == 0 as a test on words. *)
Lemma rc_eq0 rc : Int64.eq rc (Int64.repr 0) = true -> Int64.unsigned rc = 0%Z.
Proof. by have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => ->. Qed.

Lemma rc_neq0 rc : Int64.eq rc (Int64.repr 0) = false -> Int64.unsigned rc <> 0%Z.
Proof.
have := Int64.eq_spec rc (Int64.repr 0) => + H; rewrite H => Hne Hu; apply: Hne.
by rewrite -(Int64.repr_unsigned rc) Hu.
Qed.

Theorem maybe_hard_bits_ok : exp_core_spec -> decide_spec -> maybe_hard_bits_spec.
Proof.
move=> EC DE μ xb Ta Ca L2 RM r rl HT.
start; csteps.
call EC => /(_ HT) [rc0 [y' [hs' [X' [q' [q1' [rr' [h' [t' [-> [-> [Hko Hok]]]]]]]]]]]].
csteps.
case EQ: Int64.eq => /=; last first.
{ (* rc <> 0: the result stays 1 *)
  csteps; fin; split=> //.
  by rewrite /ExpModel.maybe_hard_Z (Hko (rc_neq0 _ EQ)). }
csteps.
have [Hly Hcore] := Hok (rc_eq0 _ EQ).
have [Hy Hb] := ExpModelBounds.core_bounds _ _ _ Hcore.
have E1 : forall o : 'I_1, hs' o = hs' ord0 by move=> o; rewrite (ord1 o).
have Hb' : forall o : 'I_1, - 2 ^ ExpModelBounds.hN_bits <= Int64.signed (hs' o)
             <= 2 ^ ExpModelBounds.hN_bits by move=> o; rewrite E1.
call DE => /(_ Hly Hy (Hb' _)) [Er [lo' [hi' [d' [t2 ->]]]]].
csteps.
fin; split=> //.
by rewrite Er E1 /ExpModel.maybe_hard_Z Hcore.
Qed.
