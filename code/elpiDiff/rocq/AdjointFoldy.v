(* AdjointFoldy.v — the activity, the owner and the in-place discipline of a
   fold updating an array in place, for any class of steps, and the bodies
   with branches and in-place folds whose steps end with a set (foldy), a
   subclass of nesty (AdjointNesty.v).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint
  Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops TangentGood
  AdjointCorrect AdjointBranch AdjointFold.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section Foldy.
Variable cv : bool.

(* An in-place fold with active bodies computes an array of its extent, of
   zero tangent when it is not varied. *)
Lemma act_fold_gen a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, act_body (bP x y)) -> act_value (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev.
destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction;
graph_split.
rename b into bA, b0 into bW, b1 into bD.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)),
      _ |- _ =>
  rename H into HbD end.
destruct init as [ia | |]; try contradiction.
move/in_gA: H9 => [HqL Eia]; subst ia.
destruct init0 as [iw | |]; try contradiction.
move/in_gW: H5 => [_ Eiw]; subst iw.
destruct init1 as [id | |]; try contradiction.
move/in_gD: H1 => [_ Eid]; subst id.
rewrite /= in Htc.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
case: (in_place_init _ _ _ _) Htc => // Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k))))
  Htc => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP)
  (ArrayBody (AVar (VInfo k Integer None))
     (AVar (VInfo (S k) (Array z) None)))
  (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc
  => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))))
  Htc => // -[Ete]; subst te.
move/ty_eqb_true: Etb HtB => -> HtB.
rewrite /= in Hev.
case: (aeval_atom (duals reals) (amap pd loP)) Hev => [[| l | | |] |] // Hev.
case: (aeval_atom (duals reals) (amap pd hiP)) Hev => [[| h | | |] |] // Hev.
set vr := fold_varied k (AVar (pa q)) bA.
have Hloop : forall nn z0 st,
    has_type (Array z) st -> (vr = false -> zero st) ->
    eval_fold (fun v w => aeval (duals reals) (bD v w)) z0 nn st = Some ve ->
    has_type (Array z) ve /\ (vr = false -> zero ve).
  elim=> [| nn IH] z0 st Ht Hz /= Hf.
    by case: Hf => <-.
  case Hs1: (aeval (duals reals) (bD (VInt z0) st)) Hf => [st' |] // Hf.
  set ix := PV (fresh k) (VInfo k Integer None)
    (open_index (DBound (0%nat, 0%nat))) (VInt z0) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
    (TVar (DBound (0%nat, 0%nat)) (Array z) None vr vr vr false None) st 0.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; simpl; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; simpl; auto; try lia; discriminate.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
    apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
  have [Hht Hzz] := Hab ix sx (sx :: ix :: L) (S (S k)) wP
    (PArray ix sx) (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx))
    (bD (pd ix) (pd sx)) (Array z) st'
    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB Hs1.
  apply: (IH (z0 + 1)%Z st' Hht) Hf => Hv; apply: Hzz.
  move: (Hv); rewrite /vr /fold_varied => /orb_false_iff [_ Hb'].
  by rewrite /sx /= Hv.
have [_ [_ [_ [_ [_ [_ [_ [_ [Hty Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
rewrite Eqz in Hty.
have Hz0 : vr = false -> zero (pd q).
  by rewrite /vr /fold_varied => /orb_false_iff [Hvi _]; exact: Hzq.
have [Ht Hz] := Hloop _ _ _ Hty Hz0 Hev.
by split=> //; split.
Qed.

(* An in-place fold with active bodies that is not varied leaves the tangent
   of its array as it was: zero. *)
Lemma owner_fold_gen a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, act_body (bP x y)) -> act_owner (AFold a loP hiP initP bP).
Proof.
move=> Hq Hab L k c wP pp live ty tail eA eW eD ve o HA HW HD Hs Hlv Es Ho Hev
  Hvr Hargs Hwr te Htc Hty.
have HL := s_static _ _ _ _ _ _ _ Hs.
have [Hte [Hz _]] := act_fold_gen _ _ _ _ _ Hq Hab L k wP pp tail
  eA eW eD te ve HA HW HD HL Htc Hev.
have {}Hz := Hz Hvr.
case: Hq Es => q [Eq Hqa] Es; subst initP.
case: eA HA Hvr => // aA loA hiA iA bA /= [_ [_ [HiA _]]] Hvr.
case: eW HW Hlv Htc => // aW loW hiW iW bW /= [_ [_ [HiW _]]] Hlv Htc.
case: iA HiA Hvr => // iA /in_gA [HqL EiA] Hvr; subst iA.
case: iW HiW Hlv Htc => // iW /in_gW [_ EiW] Hlv Htc; subst iW.
rewrite /= in Es.
case Eqz: (vty (pw q)) Hqa Es Htc => [| | | z] // _ [Es _].
(* the type of the fold is the type of its array *)
rewrite /= Eqz /=.
case: (_ && _) => //.
case: (in_place_init _ _ _ _) => //.
case: (occurs_anf _ _ _) => //; first by case: (varg (pw q)) => [[? ?] |].
case: (typecheck _ _ _ _) => tb [] //.
case: (ty_eqb tb (Array z)) => //.
case: (reads_around_inner_loop _ _ _) => // -[Ete]; subst te.
(* the owner is the init, live *)
have Hl : live q by apply: Hlv; rewrite /live_value /= Nat.eqb_refl orbT.
case: (s_owner _ _ _ _ _ _ _ Hs o q Ho HqL Es) => [Eqo | //]; subst o.
move/orb_false_iff: Hvr => [Hvq _].
have [_ [_ [_ [_ [_ [_ [_ [_ [Htq Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
have {}Hzq := Hzq Hvq; rewrite Eqz in Htq.
case: (pd q) Htq Hzq => // lq /= Htq Hzq.
case: ve Hte Hz {Hev} => // lv /= Htv Hzv.
congr VArray; apply: zeros_eq.
- exact/Forall_map.
- exact/Forall_map.
by rewrite !length_map Htq Htv.
Qed.

(* Outside loops, an in-place fold updates its init, the written array: the
   reverse sweep does not read it, and the fold is varied when it is. *)
Lemma inplace_fold_gen a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  inplace_only cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] L k wP pp tail eA eW te HA HW HL Hu Htc Hst Hl Hargs
  Hwr o Ho Hoin.
case: eA HA => // aA loA hiA iA bA /= [HlA [HhA [HiA HbA]]].
case: eW HW Htc => // aW loW hiW iW bW /= [HlW [HhW [HiW HbW]]] Htc.
case: iA HiA => // iA /in_gA [HqL EiA]; subst iA.
case: iW HiW Htc => // iW /in_gW [_ EiW] Htc; subst iW.
move/atom_graph: HlA => [Ela HloL]; move/atom_graph: HhA => [Eha HhiL].
move/atom_graph: HlW => [Elw _]; move/atom_graph: HhW => [Ehw _].
subst loA hiA loW hiW.
(* outside loops, the owner is the written array, the init *)
case: pp Hl Ho Htc => // _.
destruct wP as [[o' | |] |]; rewrite /=; try discriminate.
case Ey: (vty (pw o')) => [| | | ny] // [Eo]; subst o'.
case Eqz: (vty (pw q)) Hqa => [| | | z] // _.
case Eb: (_ && _) => //.
case: tail {Hst} => //.
case Eid: (vid (pw q) =? vid (pw o))%nat => //.
have Eqo : q = o by apply: Hu => //; exact/Nat.eqb_eq.
subst o.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k))))
  => //.
  by case: (varg (pw q)) => [[? ?] |].
move=> _.
(* q is varied: so is the fold; q is live: it is the init *)
split; last first.
  split; first by move=> ->.
  by move=> Hnl; exfalso; apply: Hnl; rewrite /live_value /= Nat.eqb_refl orbT.
(* the reverse sweep does not read q *)
have [_ [_ [_ [_ [_ [_ [_ [_ [Htq Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
have [Eidq [Hkq _]] := static_in _ _ _ HL HqL.
rewrite Eqz in Htq.
set vr := fold_varied k (AVar (pa q)) bA.
set ix := PV (fresh k) (VInfo k Integer None)
  (open_index (DBound (0%nat, 0%nat))) (VInt 0%Z) 0.
set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
  (TVar (DBound (0%nat, 0%nat)) (Array z) None vr vr vr false None) (pd q) 0.
have Hix : static_ok (S (S k)) ix.
  by repeat split; simpl; auto; try lia; discriminate.
have Hsx : static_ok (S (S k)) sx.
  repeat split; simpl; auto; try lia; try discriminate.
  by rewrite /vr /fold_varied => /orb_false_iff [Hvq _]; exact: Hzq.
have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
  apply: Forall_cons Hsx _; apply: Forall_cons Hix _.
  apply: Forall_impl HL => p Hp; by apply: static_mono Hp _; lia.
have Hrm : forall l0,
    atom_member (AVar (pa q))
      (atom_remove (AVar (pa sx)) (atom_remove (AVar (pa ix)) l0)) =
    atom_member (AVar (pa q)) l0.
  move=> l0; rewrite !atom_member_remove_full /same_term.
  change (aid (pa sx)) with (S k); change (aid (pa ix)) with k.
  have Hk1 : k <> aid (pa q) by lia.
  have Hk2 : S k <> aid (pa q) by lia.
  by rewrite (proj2 (Nat.eqb_neq _ _) Hk1) (proj2 (Nat.eqb_neq _ _) Hk2).
(* the bounds are integers, not q *)
have Hint : forall bnd : atom pv, (forall p, bnd = AVar p -> In p L) ->
    ty_eqb (of_atom (amap pw bnd)) Integer = true ->
    atom_member (AVar (pa q)) (atoms_of_atom (amap pa bnd)) = false.
  case=> [p | ? | ?] // Hp Ety /=.
  have HpL := Hp p erefl.
  have [Eidp _] := static_in _ _ _ HL HpL.
  rewrite /same_term Eidq Eidp orbF.
  case Epq: (vid (pw q) =? vid (pw p))%nat => //.
  have Eqp : q = p by apply: Hu => //; exact/Nat.eqb_eq.
  by subst p; move: Ety; rewrite /= Eqz.
move/andP: Eb => [Elo Ehi].
rewrite /vreads; cbn [value_needs fold_binders].
change (AV k false) with (pa ix).
change (AV (S k) (fold_varied k (AVar (pa q)) bA)) with (pa sx).
case Hn: (needs cv Replay (S (S k)) (bA (pa ix) (pa sx))) => [u l0] /=.
rewrite atom_member_union Hrm atom_member_union (Hint _ HloL Elo).
rewrite (Hint _ HhiL Ehi) /= => Ht.
have := tbr_occurs cv (sx :: ix :: L) (S (S k)) (bP ix sx)
  (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) Replay q (HbA ix _ sx _)
  (HbW ix _ sx _) HL' (or_intror (or_intror HqL)).
rewrite /tbr Hn /live_anf.
rewrite (live_cont2 L k bP bW ix sx (pw ix) (pw sx) _ HbW HL erefl erefl
  erefl erefl) Hocc.
by move=> H; have := H (or_introl Ht).
Qed.

(* Bodies of straight lets, branches, maps, scalar folds and in-place
   folds: as branchy, with also, at the top, a fold updating its array in
   place with an in-place body (abody). *)
Fixpoint foldy (top : bool) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' => foldy_value top e /\ forall x, foldy top (b' x)
  | ARet _ => True
  end
with foldy_value (top : bool) (e : value pv bare) : Prop :=
  match e with
  | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True
  | ASet _ _ _ => top = true
  | AIte _ t e => foldy false t /\ foldy false e
  | AMap _ _ b => top = true /\ forall x, foldy false (b x)
  | AFold _ _ _ init b =>
      top = true /\
      ((forall p, init = AVar p -> ~ is_array (vty (pw p))) /\
         (forall x y, foldy false (b x y)) \/
       (exists q, init = AVar q /\ is_array (vty (pw q))) /\
         (forall x y, abody (b x y)))
  end.

(* The classes of bodies are included in one another: straight, branchy,
   foldy. *)
Lemma straight_branchy (b : anf pv bare) : straight b -> branchy true b.
Proof.
elim: b => [a e b' IH | x] //= [He Hb].
split; last by move=> x; apply/IH/Hb.
by case: e He.
Qed.

Lemma branchy_foldy_mut :
  (forall b : anf pv bare, forall top, branchy top b -> foldy top b) /\
  (forall e : value pv bare, forall top,
     branchy_value top e -> foldy_value top e).
Proof.
apply: (anf_value_ind pv bare
  (fun b => forall top, branchy top b -> foldy top b)
  (fun e => forall top, branchy_value top e -> foldy_value top e)).
- move=> a e IHe b IHb top [He Hb].
  by split; [exact: (IHe top He) | move=> x; exact: (IHb x top (Hb x))].
- by [].
- by [].
- by [].
- by [].
- by [].
- move=> c t IHt e IHe top [Ht He].
  by split; [exact: (IHt false Ht) | exact: (IHe false He)].
- move=> lo hi b IHb top [Et Hb].
  by split=> // x; exact: (IHb x false (Hb x)).
move=> a lo hi init b IHb top [Et [Hna Hb]].
by split=> //; left; split=> // x y; exact: (IHb x y false (Hb x y)).
Qed.

Lemma branchy_foldy top (b : anf pv bare) : branchy top b -> foldy top b.
Proof. exact: (proj1 branchy_foldy_mut). Qed.

End Foldy.
