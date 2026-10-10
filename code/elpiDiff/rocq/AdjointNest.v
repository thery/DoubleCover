(* AdjointNest.v — the reverse sweep of nested in-place folds: an in-place
   fold whose body ends with an inner in-place fold on its state (fbody).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect AdjointBranch
  AdjointFold AdjointFoldy.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section Nest.
Variable cv : bool.

(* The adjoint simulation of a nest body: scalar lets, then the inner
   in-place fold. *)
Lemma fbody_asim (bP : anf pv bare) : fbody bP -> asim_body cv bP.
Proof.
elim: bP => [a e cP IH | x] //=.
case: e => //.
- move=> f aP Hb.
  apply: asim_let; [exact: afwd_op1 | | exact: inplace_straight | exact: act_op1 |
    exact: owner_op1 | by move=> y; exact: IH (Hb y)].
  apply: asim_rev_bars; [exact: arev_op1 | by apply: straight_rev_bars |
    by apply: straight_no_top | by []].
- move=> f aP bP0 Hb.
  apply: asim_let; [exact: afwd_op2 | | exact: inplace_straight | exact: act_op2 |
    exact: owner_op2 | by move=> y; exact: IH (Hb y)].
  apply: asim_rev_bars; [exact: arev_op2 | by apply: straight_rev_bars |
    by apply: straight_no_top | by []].
- move=> aP iP Hb.
  apply: asim_let; [exact: afwd_get | | exact: inplace_straight | exact: act_get |
    exact: owner_get | by move=> y; exact: IH (Hb y)].
  apply: asim_rev_bars; [exact: arev_get | by apply: straight_rev_bars |
    by apply: straight_no_top | by []].
move=> fa loP hiP [s | ? | ?] bi //= [Hs [Hab Hret]].
have Hq : exists q, AVar s = AVar q /\ is_array (vty (pw q)) by exists s.
apply: asim_let.
- by apply: afwd_fold_inplace.
- by apply: arev_fold_inplace.
- by apply: inplace_fold_inplace.
- by apply: act_fold_inplace.
- by apply: owner_fold_inplace.
by move=> y; rewrite Hret; exact: asim_ret.
Qed.

Lemma adj_replay_fbody (bP : anf pv bare) : fbody bP ->
  forall L k w vo bA bT se c, anf_eq (gA L) bP bA -> anf_eq (gT L) bP bT ->
  let '((fb, _), _) := open_pairs (adj W w vo Replay (rebuild _ bT (annotate_body_t cv Replay k bA)) se) c in
  forall s s1, run fb s = Some s1 -> forall v, below c v -> consistent v -> store_get s1 (keyv v) = store_get s (keyv v).
Proof.
elim: bP => [a e cP IH | x] //= Hab L k w vo bA bT se c HA HT.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
case: bT HT => [aT eT cT | ?] //= [HeT HcT].
cbn [annotate_body_t].
case Enl: (needs cv Replay (S k) (cA (let_binder k eA))) => [u l].
have Cc : consistent (DBound (c, c) : dvar W) by [].
(* a defined variable is fresh: the variables below c keep their values *)
have Hdef : forall so e0 s0 sa v, run [DDefine so (DBound (c, c)) e0] s0 = Some sa -> below c v -> consistent v ->
    store_get sa (keyv v) = store_get s0 (keyv v).
{ move=> so e0 s0 sa v /run_define_inv [w0 ->] Hb Hcv.
  apply: store_get_set_other => K.
  by move: (keyv_inj _ _ Cc Hcv K) Hb => <- /=; lia. }
(* the rest of the body, opened at S c *)
have Hrest : (forall y, fbody (cP y)) -> forall t vr,
  let '((fb', _), _) := open_pairs (adj W w vo Replay (rebuild _ (cT (open_let t (DBound (c, c)) vr false))
                           (annotate_body_t cv Replay (S k) (cA (let_binder k eA)))) se) (S c) in
  forall s s1, run fb' s = Some s1 -> forall v, below (S c) v -> consistent v -> store_get s1 (keyv v) = store_get s (keyv v).
  by move=> Hb t vr; exact: (IH (PV (let_binder k eA) (VInfo k Real None) (open_let t (DBound (c, c)) vr false) (VInt 0) 0)
                              (Hb _) (_ :: L) (S k) w vo _ _ se (S c) (HcA _ _) (HcT _ _)).
case: e Hab HeA HeT => // [f0 a0 | f0 a0 b0 | a0 i0 | fa0 lo0 hi0 i0 bi0] Hab HeA HeT.
(* a scalar let: the replay defines its binder, if needed, then replays the rest *)
- case: eA HeA Enl HcA Hrest => // f1 a1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // f2 a2 _ HcT Hrest.
  have := Hrest Hab (type_of (AOp1 f2 a2)) (varied_value k (AOp1 f1 a1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
- case: eA HeA Enl HcA Hrest => // f1 a1 b1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // f2 a2 b2 _ HcT Hrest.
  have := Hrest Hab (type_of (AOp2 f2 a2 b2)) (varied_value k (AOp2 f1 a1 b1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
- case: eA HeA Enl HcA Hrest => // a1 i1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // a2 i2 _ HcT Hrest.
  have := Hrest Hab (type_of (AGet a2 i2)) (varied_value k (AGet a1 i1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
(* the final fold: the reverse sweep does not read it (needs of a return in
   Replay is empty), so it is not replayed *)
case: eA HeA Enl HcA Hrest => // fa1 lo1 hi1 i1 b1 _ Enl HcA _.
case: eT HeT HcT => // fa2 lo2 hi2 i2 b2 _ HcT.
case: (i0) Hab => [s0 | ? | ?] // [_ [_ Hret]].
have El : l = [].
  have := HcA (PV (let_binder k (AFold fa1 lo1 hi1 i1 b1)) (VInfo k Real None)
    dummy_tvar (VInt 0) 0) (let_binder k (AFold fa1 lo1 hi1 i1 b1)).
  by rewrite Hret; move: Enl; case: (cA _) => //= r [_ <-] _.
rewrite El /=.
have EcT : forall y, exists r, cT y = ARet r.
  move=> y; have := HcT (PV (AV k false) (VInfo k Real None) y (VInt 0) 0) y.
  by rewrite Hret; case: (cT y) => //= r _; exists r.
case: i2 => [a3 | s3 | z3] /=.
all: cbn [open_pairs]; rewrite ?open_pairs_sbind.
+ set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
  case Ety: (tty a3) => [| | | z0].
  - cbn [open_pairs].
    case: (EcT (open_let Real (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  - cbn [open_pairs].
    case: (EcT (open_let Integer (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  - cbn [open_pairs].
    case: (EcT (open_let Boolean (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  case: (EcT (open_let (Array z0) (tstored a3) vr (trecorded a3))) => r ->.
  cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
  case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
  by move=> s1 s2; rewrite /run /= => -[<-].
+ set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
  case: (EcT (open_let Real (DBound (c, c)) vr false)) => r ->.
  cbn [rebuild adj sweep_eqb open_pairs sbind]; rewrite open_pairs_sbind.
  case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
  by move=> s1 s2; rewrite /run /= => -[<-].
set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
case: (EcT (open_let Integer (DBound (c, c)) vr false)) => r ->.
cbn [rebuild adj sweep_eqb open_pairs sbind]; rewrite open_pairs_sbind.
case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
by move=> s1 s2; rewrite /run /= => -[<-].
Qed.

End Nest.
