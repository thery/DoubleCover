(* AdjointNestFwd.v — the forward sweep of nested in-place folds: an outer
   in-place fold whose body (fbody) is made of scalar lets ending with an
   inner in-place fold on the state of the outer one.

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

Section NestFwd.
Variable cv : bool.

(* The inner in-place fold that ends the body of the outer loop: it updates
   the state in place, pushing the elements its steps overwrite. *)
Lemma psim_fold_let a a' (loP hiP : atom pv) (s : pv)
  (bi : pv -> pv -> anf pv bare) (cP : pv -> anf pv bare) :
  is_array (vty (pw s)) -> (forall x y, abody (bi x y)) ->
  (forall x, cP x = ARet (AVar x)) ->
  psim_body cv (ALet a (AFold a' loP hiP (AVar s) bi) cP).
Proof.
move=> Hsa Hab HcP L k c st wP pp m m'.
move=> [aA eA cA | ?] [aW eW cW | ?] [aT eT cT | ?] [aD eD cD | ?] ty v;
  move=> HA HW HT HD Hc Htc Hev Htp0; rewrite /= in HA HW HT HD; try by [].
case: HA HW HT HD => [HeA HcA] [HeW HcW] [HeT HcT] [HeD HcD].
rewrite /= in Htc Hev.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
  (WellFormed.is_tail cW k) k eW) Htc => [te []] // Htc.
case Hve: (aeval_value (duals reals) eD) Hev => [ve |] // Hev.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
set eP := AFold a' loP hiP (AVar s) bi.
set tail := WellFormed.is_tail cW k in Hte.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Es : storage wP tail eP = Some (stored s).
  by rewrite /eP /=; case: (vty (pw s)) Hsa.
have Hsn : storage wP tail eP <> None by rewrite Es.
have HeA0 : value_eq (gA L) eP eA by exact: HeA.
have HeW0 : value_eq (gW L) eP eW by exact: HeW.
have HeT0 : value_eq (gT L) eP eT by exact: HeT.
have HeD0 : value_eq (gD L) eP eD by exact: HeD.
have [Ht [o [Ho Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW0 Hte
  Htail_ty (or_introl Hsn).
(* the four versions of the fold, on the state s *)
destruct eA as [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ?
               | fa loA hiA [sA | ? | ?] bA];
  try contradiction; case: HeA => [_ [_ [HsA HbA]]]; try contradiction.
destruct eW as [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ?
               | fw loW hiW [sW | ? | ?] bW];
  try contradiction; case: HeW => [_ [_ [HsW HbW]]]; try contradiction.
destruct eT as [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ?
               | ft loT hiT [sT | ? | ?] bT];
  try contradiction; case: HeT => [_ [_ [HsT HbT]]]; try contradiction.
destruct eD as [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ?
               | fd loD hiD [sD | ? | ?] bD];
  try contradiction; case: HeD => [_ [_ [HsD HbD]]]; try contradiction.
move/in_gA: HsA => [HsL EsA]; move/in_gW: HsW => [_ EsW].
move/in_gT: HsT => [_ EsT]; move/in_gD: HsD => [_ EsD].
subst sA sW sT sD.
(* the state is the owner *)
have Hlive_s :
    live_anf k (ALet aW (AFold fw loW hiW (AVar (pw s)) bW) cW) s.
  by rewrite /live_anf /= Nat.eqb_refl /= ?orb_true_r.
have Eso : s = o.
  have Epn : pn s = pn o by move: Es'; rewrite Es => -[] ->.
  by case: (s_owner _ _ _ _ _ _ _ Hs o s Ho HsL Epn).
subst o.
have Ety := Htail_ty Ht; subst ty.
have Haid := aids_below L k HL.
set eA := AFold fa loA hiA (AVar (pa s)) bA.
set vr := varied_value k eA; set rec := trecorded (pt s).
set x := PV (let_binder k eA) (VInfo k te None)
  (open_let te (stored s) vr rec) ve (pn s).
have Hx : aid (pa x) = k by [].
have HxL : ~ In x L by exact: (fresh_notin L k x Haid Hx).
have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
have ET : cT (pt x) = ARet (AVar (pt x)).
  have := HcT x (pt x); rewrite Hcx.
  case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
    by case: E => <-.
  by case/in_gT: I => I _; case: HxL.
have ED : cD (pd x) = ARet (AVar (pd x)).
  have := HcD x (pd x); rewrite Hcx.
  case: (cD (pd x)) => [? ? ? | [t' | |]] //= [E | I].
    by case: E => <-.
  by case/in_gD: I => I _; case: HxL.
have EA : cA (pa x) = ARet (AVar (pa x)).
  have := HcA x (pa x); rewrite Hcx.
  case: (cA (pa x)) => [? ? ? | [t' | |]] //= [E | I].
    by case: E => <-.
  by case/in_gA: I => I _; case: HxL.
rewrite /= in ET ED EA; rewrite ED /= in Hev; case: Hev => Ev; subst v.
have [_ [_ [Hstq [Htyq _]]]] := static_in _ _ _ HL HsL.
(* the code: the fold computed into the storage of s, then x *)
cbn [annotate_body_t].
case: (needs cv m' (S k) _) => [u0 l0].
cbn [rebuild]; rewrite prim_let; cbv [let_ann].
set vt := annotate_value_t cv k eA.
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW0 HeT0 HL Hte).
have Ews : forall Bc
    (K : dvar W -> bool -> scoped W (list (dstmt W) * dexpr W)),
    with_storage (option_map (amap pt) wP)
      (rebuild_value _ (AFold ft loT hiT (AVar (pt s)) bT) vt) Bc K =
    K (stored s) rec.
  move=> Bc K; rewrite /vt /eA /=.
  by rewrite Htyq; case: (vty (pw s)) Hsa => // ? _; rewrite Hstq.
rewrite Ews -/x -/vr ET EA.
cbn [annotate_body_t rebuild prim].
(* the innermost fold of the body is the fold, live when it records *)
have Htl : tail_live cv k (ALet aA eA cA) = fold_live cv k (AVar (pa s)) bA.
  rewrite /tail_live /= -/eA EA /fold_live /=.
  by case: (tail_fold_live _ _ _).
have Hfl := fold_live_abody cv L k bi (AVar (pa s)) bA Hab HbA.
have Hrecs : records cv k eA = true -> fold_live cv k (AVar (pa s)) bA = true.
  rewrite Hfl /= => /orP [H | H].
    exact: H.
  set ix := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
  set sx := PV (AV (S k) (fold_varied k (AVar (pa s)) bA))
    (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
  have Hb : anf_eq (gA (sx :: ix :: L)) (bi ix sx)
      (bA (AV k false) (AV (S k) (fold_varied k (AVar (pa s)) bA))).
    exact: HbA.
  by rewrite (records_in_abody cv _ (Hab ix sx) _ _ _ Hb) in H.
(* the forward sweep of the fold *)
have IHf := afwd_fold_inplace cv a' loP hiP (AVar s) bi
  (ex_intro _ s (conj erefl Hsa)) Hab.
have Hlv_e : forall p, live_value k (AFold fw loW hiW (AVar (pw s)) bW) p ->
    live_anf k (ALet aW (AFold fw loW hiW (AVar (pw s)) bW) cW) p.
  by move=> p; rewrite /live_value /live_anf /= => ->.
have Hc1 : actx L k c st wP pp
    (live_value k (AFold fw loW hiW (AVar (pw s)) bW)) (vatoms k eA) te.
  apply: (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); last by lia.
  by move=> p Hp Hv; apply: Hlv_e; exact: vatoms_live HeA0 HeW0 HL Hp Hv.
have Hj : exists j, stored s = DBound (j, j) /\ (j < c)%nat.
  by exists (pn s); split=> //; exact: (s_num _ _ _ _ _ _ _ Hs s HsL).
have Hst0 : match storage wP tail eP return Prop with
    | Some m0 => stored s = m0
    | None => forall p, In p L -> stored p <> stored s end by rewrite Es.
have Hrec' : rec = true \/ (m = Forward /\ records cv k eA = true /\
    storage wP tail eP <> None /\ ~ not_in_loop pp) ->
    exists l0, store_get st (keyv (TapeOf (stored s))) = Some (VTape l0).
  case=> [Er | [Em [Hr _]]].
    exact: (a_tape _ _ _ _ _ _ _ _ _ Hc s HsL Er).
  by apply: (Htp0 s Ho); rewrite -/eA Htl (Hrecs Hr) Em.
have IH := IHf L k c st wP pp tail eA _ _ _ te (stored s) ve te m rec
  HeA0 HeW0 HeT0 HeD0 Hc1 Hte Htail_ty Hj Hst0 Hrec' Hve.
cbv zeta in IH; rewrite -/vt in IH.
rewrite open_pairs_sbind.
case Hfe: (open_pairs (fwd_value _ _ _ _ _ _ _) c) IH => [se c1] IH.
cbn [open_pairs sbind].
case: IH => Hcc1 [s1 [R1 [F1 [T1 [S1 [_ G1]]]]]].
have Hex : inplace wP pp = Some (stored s) by rewrite /inplace Ho.
split=> //; exists s1; rewrite app_nil_r Hex.
split=> //; split=> //; split=> //.
split; first exact: S1.
move=> o; rewrite Ho => -[<-] _.
split=> //.
(* the tape: in a loop body, the pushes of the steps of the fold *)
move=> /andP [Hm Hcnd] Htid l1 Hl1.
have Em : m = Forward by case: (m) Hm.
have Hnl : ~ not_in_loop pp.
  by move=> Hnl; exact: (a_tid _ _ _ _ _ _ _ _ _ Hc s Ho Hnl Htid).
have Hto : forall o, owner wP pp = Some o -> tid (pt o) = None.
  by move=> o'; rewrite Ho => -[<-].
have := G1 Em Hnl Hsn Hto; rewrite /fold_grow.
move: Hve; rewrite /=.
case: (aeval_atom _ loD) => [[| l | | |] |] //.
case: (aeval_atom _ hiD) => [[| h | | |] |] // Hev'.
rewrite Hev' ED.
have [tr Htr] := fold_trace_exists _ _ _ _ _ Hev'.
rewrite Htr fold_pushes_fix => G.
have Hcnd' : fold_live cv k (AVar (pa s)) bA || rec = true.
  by rewrite orbC /rec -Htl.
exact: (G tr erefl Hcnd' l1 Hl1).
Qed.

(* The bodies of the outer loop of a nest: their forward sweep. *)
Lemma fbody_psim b : fbody b -> psim_body cv b.
Proof.
elim: b => [a e b' IH | x] //=.
case: e => // [? ? | ? ? ? | ? ? | fa lo hi [s | ? | ?] bi] //= Hb.
- apply: psim_let; [exact: afwd_op1 | exact: act_op1 | by [] | by [] |].
  by move=> x; apply/IH/Hb.
- apply: psim_let; [exact: afwd_op2 | exact: act_op2 | by [] | by [] |].
  by move=> x; apply/IH/Hb.
- apply: psim_let; [exact: afwd_get | exact: act_get | by [] | by [] |].
  by move=> x; apply/IH/Hb.
case: Hb => [Hsa [Hab Hc]].
exact: psim_fold_let.
Qed.

(* The forward sweep of a nest of in-place folds. *)
Lemma afwd_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> Hq Hfb; apply: afwd_fold_body => // x y.
- exact: fbody_psim.
- exact: fbody_act.
exact: fbody_ibody.
Qed.

End NestFwd.
