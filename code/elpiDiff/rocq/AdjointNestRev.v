(* AdjointNestRev.v — facts for the reverse sweep of nested in-place folds:
   the innermost fold of the body of the outer loop (fbody) is its tail
   fold, varied, and the outer loop records iff that fold is live.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect AdjointBranch
  AdjointFold AdjointFoldy AdjointNestSide.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section NestRev.
Variable cv : bool.

(* The innermost fold of an fbody is live iff the body records. *)
Lemma fbody_tail_live (bP : anf pv bare) : fbody bP ->
  forall L k bA, anf_eq (gA L) bP bA ->
  tail_fold_live cv k bA = Some (records_in cv k bA).
Proof.
elim: bP => [a e c IH | x] //= Hfb L k bA HA.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have Hrec : (forall y, fbody (c y)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) =
    Some (records_in cv (S k) (cA (let_binder k eA))).
  by move=> Hb; exact: IH x (Hb x) (x :: L) (S k) _ (HcA x _).
clearbody x.
case: e Hfb HeA => // [f0 a0 | f0 a0 b0 | a0 i0 | fa lo hi [s | ? | ?] bi]
  //= Hfb HeA.
- by case: eA HeA Hrec => //= ? ? _ Hrec; rewrite Hrec.
- by case: eA HeA Hrec => //= ? ? ? _ Hrec; rewrite Hrec.
- by case: eA HeA Hrec => //= ? ? _ Hrec; rewrite Hrec.
case: Hfb => [_ [Hab Hc]].
case: eA HeA x Hrec => // fa' lo' hi' iA biA [_ [_ [_ HbA]]] x _.
have [r Er] : exists r, cA (let_binder k (AFold fa' lo' hi' iA biA)) = ARet r.
  have := HcA x (let_binder k (AFold fa' lo' hi' iA biA)); rewrite Hc.
  by case: (cA _) => // r _; exists r.
rewrite Er /=.
set i := AV k false; set sv := AV (S k) (fold_varied k iA biA).
set ix := PV i (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set sx := PV sv (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
have Hb : anf_eq (gA (sx :: ix :: L)) (bi ix sx) (biA i sv) by exact: HbA.
rewrite (tail_fold_live_abody cv _ (Hab ix sx) _ (S (S k)) _ Hb).
by rewrite (records_in_abody cv _ (Hab ix sx) _ _ _ Hb) /state_live /= !orbF.
Qed.

(* The innermost fold of an fbody, on the state sx of the outer loop, is
   varied when sx is: the tail fold state of the body is its liveness. *)
Lemma fbody_tail_state (bP : anf pv bare) : fbody bP ->
  forall L k wP ix sx bA bW te,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW ->
  (forall p, In p L -> (vid (pw p) < k)%nat) -> (vid (pw sx) < k)%nat ->
  (forall p, In p L -> vid (pw p) = vid (pw sx) -> p = sx) ->
  avaried (pa sx) = true ->
  typecheck (option_map (amap pw) wP) (ArrayBody (AVar (pw ix)) (AVar (pw sx)))
    k bW = (te, Ok) ->
  tail_fold_state cv k bA = tail_fold_live cv k bA.
Proof.
elim: bP => [a e c IH | x] //= Hfb L k wP ix sx bA bW te HA HW Hk Hsk Hu Hvs.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
case: bW HW => [aW eW cW | ?] //= [HeW HcW] Htc.
case Hte: (typecheck_value _ _ _ _ eW) Htc => [te0 []] // Htc.
set x := PV (let_binder k eA) (VInfo k te0 None) dummy_tvar (VInt 0) 0.
have Hrec : (forall y, fbody (c y)) ->
    tail_fold_state cv (S k) (cA (let_binder k eA)) =
    tail_fold_live cv (S k) (cA (let_binder k eA)).
  move=> Hb.
  apply: (IH x (Hb x) (x :: L) (S k) wP ix sx _ _ te (HcA x _) (HcW x _))
    => //.
  - by move=> p [<- | Hp] //=; have := Hk p Hp; lia.
  - by lia.
  move=> p [<- | Hp] /= E; first by lia.
  exact: Hu.
clearbody x.
case: e Hfb HeA HeW Hte
  => // [f0 a0 | f0 a0 b0 | a0 i0 | fa lo hi [s | ? | ?] bi] //=
  Hfb HeA HeW Hte.
- by case: eA HeA Hrec => //= ? ? _ Hrec; rewrite Hrec.
- by case: eA HeA Hrec => //= ? ? ? _ Hrec; rewrite Hrec.
- by case: eA HeA Hrec => //= ? ? _ Hrec; rewrite Hrec.
case: Hfb => [_ [Hab Hc]].
case: eA HeA Hrec => // fa' lo' hi' [sA | ? | ?] biA [_ [_ [HsA HbA]]] _ //.
case: eW HeW Hte => // fw lw hw [sW | ? | ?] biW [_ [_ [HsW _]]] Hte //.
move/in_gA: HsA => [HsL EsA]; move/in_gW: HsW => [_ EsW]; subst sA sW.
set eA := AFold fa' lo' hi' (AVar (pa s)) biA.
set y := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have HyL : ~ In y L by move=> I; have := Hk y I; rewrite /=; lia.
have EA : cA (let_binder k eA) = ARet (AVar (let_binder k eA)).
  have := HcA y (let_binder k eA); rewrite Hc.
  case: (cA _) => [? ? ? | [t' | |]] //= [E | I].
    by case: E => <-.
  by case/in_gA: I => I _; case: HyL.
rewrite EA /= Nat.eqb_refl.
rewrite /= in Hte.
(* the inner fold is on the state sx, by its typing *)
have Evid : (vid (pw s) =? vid (pw sx))%nat = true.
  move: Hte; case: (_ && _) => //; case: (ty_eqb _ Real) => //.
  case: (vty (pw s)) => // n; case: (WellFormed.is_tail cW k) => //.
  by case: (vid (pw s) =? vid (pw sx))%nat.
have Ess : s = sx by apply: Hu => //; exact/Nat.eqb_eq.
subst s.
rewrite Hvs /=.
set i := AV k false; set sv := AV (S k) (fold_varied k (AVar (pa sx)) biA).
set ix' := PV i (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set sx' := PV sv (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
have Hb : anf_eq (gA (sx' :: ix' :: L)) (bi ix' sx') (biA i sv) by exact: HbA.
rewrite (tail_fold_live_abody cv _ (Hab ix' sx') _ (S (S k)) _ Hb).
by rewrite (fold_live_abody cv L k bi _ biA Hab HbA).
Qed.

(* The outer fold of a nest is live iff its body records. *)
Lemma fold_live_nest L k (bP : pv -> pv -> anf pv bare) initA bA :
  (forall x y, fbody (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  fold_live cv k initA bA =
  records_in cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))).
Proof.
move=> Hfb HbA; rewrite /fold_live /fold_binders.
set i := AV k false; set sv := AV (S k) (fold_varied k initA bA).
set ix := PV i (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set sx := PV sv (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
have Hb : anf_eq (gA (sx :: ix :: L)) (bP ix sx) (bA i sv) by exact: HbA.
by rewrite (fbody_tail_live _ (Hfb ix sx) _ _ _ Hb).
Qed.

(* The outer loop of a nest records iff it is live: its state is dead. *)
Lemma records_fold_nest L k fa (loA hiA : atom avar)
  (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
  (forall x y, fbody (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  Forall (static_ok k) L -> ids_unique L ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) ->
  reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))) =
    false ->
  records cv k (AFold fa loA hiA initA bA) = fold_live cv k initA bA.
Proof.
move=> Hfb HbA HbW HL Hu HtB Hra.
have Hd := fbody_state_dead cv L k bP bA bW initA z wP Hfb HbA HbW HL Hu HtB
  Hra.
rewrite (fold_live_nest L k bP initA bA Hfb HbA).
by move: Hd; rewrite /state_live /= => ->.
Qed.

(* The step of the outer loop of a nest, varied, ends with its innermost
   fold, whose liveness is the one of the outer loop. *)
Lemma tail_state_nest L k (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
  (forall x y, fbody (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  Forall (static_ok k) L -> fold_varied k initA bA = true ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) ->
  tail_fold_state cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) =
    Some (fold_live cv k initA bA) /\
  tail_live cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) =
    fold_live cv k initA bA.
Proof.
move=> Hfb HbA HbW HL Hvr HtB.
set vr := fold_varied k initA bA in Hvr *.
set ix := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None) dummy_tvar (VInt 0) 0.
have Hb : anf_eq (gA (sx :: ix :: L)) (bP ix sx) (bA (pa ix) (pa sx)).
  exact: HbA.
have Hbw : anf_eq (gW (sx :: ix :: L)) (bP ix sx) (bW (pw ix) (pw sx)).
  exact: HbW.
have Hk : forall p, In p (sx :: ix :: L) -> (vid (pw p) < S (S k))%nat.
  move=> p [<- | [<- | Hp]] /=; try lia.
  by have [_ [Hlt _]] := static_in _ _ _ HL Hp; lia.
have Hu : forall p, In p (sx :: ix :: L) -> vid (pw p) = vid (pw sx) -> p = sx.
  move=> p [<- | [<- | Hp]] //= E; first by lia.
  by have [_ [Hlt _]] := static_in _ _ _ HL Hp; lia.
have Hsk : (vid (pw sx) < S (S k))%nat by rewrite /=; lia.
have Hts := fbody_tail_state _ (Hfb ix sx) (sx :: ix :: L) (S (S k)) wP ix sx
  _ _ _ Hb Hbw Hk Hsk Hu Hvr HtB.
have Hl := fbody_tail_live _ (Hfb ix sx) _ (S (S k)) _ Hb.
rewrite (fold_live_nest L k bP initA bA Hfb HbA) -/vr.
change (bA (AV k false) (AV (S k) vr)) with (bA (pa ix) (pa sx)).
by rewrite Hts /tail_live Hl.
Qed.

End NestRev.
