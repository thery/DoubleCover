(* AdjointNestSide.v — the in-place folds whose bodies are themselves
   nests (fbody): their activity, their owner and the in-place discipline,
   as in AdjointFoldy.v for the in-place folds with abody bodies.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint
  Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops TangentGood
  AdjointCorrect AdjointBranch AdjointFold AdjointFoldy.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section NestSide.
Variable cv : bool.

(* A body of the outer loop of a nest computes a value of its type, of zero
   tangent when it is not varied. *)
Lemma fbody_act_side b : fbody b -> act_body b.
Proof.
elim: b => [a e b' IH | x] //=.
case: e => // [? ? | ? ? ? | ? ? | a1 lo1 hi1 [s | ? | ?] bi] //= Hb.
- by apply: act_let; [exact: act_op1 | move=> x; apply/IH/Hb].
- by apply: act_let; [exact: act_op2 | move=> x; apply/IH/Hb].
- by apply: act_let; [exact: act_get | move=> x; apply/IH/Hb].
case: Hb => Hs [Hbi Hret].
apply: act_let; first by apply: act_fold_inplace => //; exists s.
by move=> x; rewrite (Hret x); exact: act_ret.
Qed.

(* An in-place fold with nest bodies computes an array of its extent, of
   zero tangent when it is not varied. *)
Lemma act_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> act_value (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev.
destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction;
repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : atom_eq (gA _) _ _ |- _ =>
         apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gW _) _ _ |- _ =>
         apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gD _) _ _ |- _ =>
         apply atom_graph in H; destruct H as [-> ?]
       end; subst.
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
  have [Hht Hzz] := fbody_act_side _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP
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

(* Not varied, it leaves the tangent of its array as it was: zero. *)
Lemma owner_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> act_owner (AFold a loP hiP initP bP).
Proof.
move=> Hq Hab L k c wP pp live ty tail eA eW eD ve o HA HW HD Hs Hlv Es Ho Hev
  Hvr Hargs Hwr te Htc Hty.
have HL := s_static _ _ _ _ _ _ _ Hs.
have [Hte [Hz _]] := act_fold_nest _ _ _ _ _ Hq Hab L k wP pp tail
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

(* Outside loops, it updates its init in place: the reverse sweep does not
   read it, and the fold is varied when it is. *)
Lemma inplace_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> inplace_only cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k wP pp tail eA eW te HA HW HL Hu Htc Hst Hl Hargs
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

(* A body of the outer loop of a nest ends with its inner fold. *)
Lemma fbody_ends G k (bP : anf pv bare) bW :
  fbody bP -> anf_eq G bP bW ->
  (forall p w, In (p, w) G -> (aid (pa p) < k)%nat) ->
  ends_with_fold k bW = true.
Proof.
elim: bP G k bW => [a e b' IH | x] G k [aW eW cW | ?] //= Hb [HeW HcW] Hlt.
have Hlt' : forall p w, In (p, w) ((opened k, anon k) :: G) ->
    (aid (pa p) < S k)%nat.
  by move=> p w [[<- _] | I] /=; [lia | have := Hlt _ _ I; lia].
case: e Hb HeW => // [? ? | ? ? ? | ? ? | a1 lo1 hi1 [s | ? | ?] bi] //= Hb.
- by case: eW => //= *; exact: (IH _ _ _ _ (Hb _) (HcW _ _) Hlt').
- by case: eW => //= *; exact: (IH _ _ _ _ (Hb _) (HcW _ _) Hlt').
- by case: eW => //= *; exact: (IH _ _ _ _ (Hb _) (HcW _ _) Hlt').
case: eW => // aW' loW hiW iW bW' _; case: Hb => _ [_ Hret].
have := HcW (opened k) (anon k); rewrite Hret /WellFormed.is_tail.
case: (cW (anon k)) => [? ? ? | [v | ? | ?]] //= [Ev | I].
  by case: Ev => <-; rewrite Nat.eqb_refl.
by have := Hlt _ _ I; rewrite /=; lia.
Qed.

(* Two openings of a binder at k that agree on its identifier. *)
Lemma agree_cons G1 G2 k x w1 w2 :
  agree G1 G2 k -> aid (pa x) = k -> vid w1 = vid w2 ->
  agree ((x, w1) :: G1) ((x, w2) :: G2) (S k).
Proof.
move=> [H1 H2] Hx Hw; split.
  move=> p u1 u2 [E1 | I1] [E2 | I2].
  - by case: E1 => _ <-; case: E2 => _ <-.
  - by case: E1 => E1 _; subst p; have := H2 _ _ (or_intror I2); lia.
  - by case: E2 => E2 _; subst p; have := H2 _ _ (or_introl I1); lia.
  exact: H1 I1 I2.
move=> p w [[E | I] | [E | I]].
- by case: E => <- _; lia.
- by have := H2 _ _ (or_introl I); lia.
- by case: E => <- _; lia.
by have := H2 _ _ (or_intror I); lia.
Qed.

(* An integer atom is not the variable j, of array type. *)
Lemma int_atom_not G G1 k j (aP : atom pv) aA aW aW1 :
  atom_eq (gA G) aP aA -> atom_eq (gW G) aP aW -> atom_eq G1 aP aW1 ->
  agree G1 (gW G) k -> (forall q, In q G -> aid (pa q) = vid (pw q)) ->
  (forall p w, In (p, w) G1 -> vid w = j -> vty w <> Integer) ->
  ty_eqb (of_atom aW1) Integer = true ->
  atom_member (AVar (AV j false)) (atoms_of_atom aA) = false.
Proof.
move=> HA HW HW1 [Hag _] Hid Hty Ei.
rewrite (atoms_atom G aP aA aW j HA HW Hid).
case: aP HA HW HW1 => [p | ? | ?]; case: aW => [w | ? | ?] //=;
  case: aW1 Ei => [w1 | ? | ?] //= Ei _ Hw Hw1.
have Ew := Hag _ _ _ Hw1 Hw.
case Ej: (vid w =? j)%nat => //.
move/Nat.eqb_eq: Ej => Ej.
by have := Hty _ _ Hw1; rewrite Ew => /(_ Ej); move/ty_eqb_true: Ei.
Qed.

(* The replay of a body of the outer loop of a nest does not read the
   variable j, the state of the outer loop: the lets before the inner fold
   do not mention it, the bounds of the inner fold are integers and its
   body does not read its init. *)
Lemma fbody_needs (bP : anf pv bare) : fbody bP ->
  forall G G1 bA bW bW1 k j wr ix sv t,
  anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> anf_eq G1 bP bW1 ->
  agree G1 (gW G) k -> (forall q, In q G -> aid (pa q) = vid (pw q)) ->
  (forall p w, In (p, w) G1 -> vid w = j -> vty w <> Integer) ->
  (j < k)%nat -> vid sv = j ->
  typecheck wr (ArrayBody ix (AVar sv)) k bW1 = (t, Ok) ->
  reads_around_inner_loop j k bW = false ->
  atom_member (AVar (AV j false)) (snd (needs cv Replay k bA)) = false.
Proof.
elim: bP => [a e b' IH | x] //= Hb G G1 [aA eA cA | ?] [aW eW cW | ?]
  [aW1 eW1 cW1 | ?] k j wr ix sv t //= [HeA HcA] [HeW HcW] [HeW1 HcW1]
  Hag Hid Hty Hjk Hsv Htc Hra.
case Ete: (typecheck_value _ _ _ _ _) Htc => [te []] //= Htc.
set x1 := PV (let_binder k eA) (anon k) dummy_tvar (VInt 0%Z) 0.
have Hid' : forall q, In q (x1 :: G) -> aid (pa q) = vid (pw q).
  by move=> q [<- | Hq] //; exact: Hid.
have Hag' : agree ((x1, VInfo k te None) :: G1) (gW (x1 :: G)) (S k).
  by apply: agree_cons.
have Hty' : forall p w, In (p, w) ((x1, VInfo k te None) :: G1) ->
    vid w = j -> vty w <> Integer.
  by move=> p w [[_ <-] /= | I]; [lia | exact: Hty I].
have HjS : (j < S k)%nat by lia.
(* a let before the tail: it does not mention j *)
have Hop : (forall x, fbody (b' x)) ->
    occurs_value j k eW = false ->
    reads_around_inner_loop j (S k) (cW (anon k)) = false ->
    atom_member (AVar (AV j false)) (snd (needs cv Replay k
      (ALet aA eA cA))) = false.
  move=> Hb' Hocc Hra'.
  have IHc := IH x1 (Hb' x1) (x1 :: G) _ _ _ (cW1 (VInfo k te None)) (S k) j
    wr ix sv t (HcA _ _) (HcW _ _) (HcW1 _ _) Hag' Hid' Hty' HjS Hsv Htc Hra'.
  rewrite /=.
  case Eb: (needs cv Replay (S k) (cA (let_binder k eA))) IHc => [ub lb] IHc.
  rewrite /= in IHc.
  have Hrd : forall rd fl, value_needs cv k eA = (rd, fl) ->
      atom_member (AVar (AV j false)) rd = false.
    move=> rd fl Ev; case Er: (atom_member _ rd) => //.
    have := (proj2 (needs_occurs cv)) e G eA eW k j HeA HeW Hid Hjk.
    by rewrite Ev /= Er Hocc => /(_ erefl).
  have Hat := (proj2 atoms_occurs) e G eA eW k j HeA HeW Hid Hjk.
  case: (_ && _); last first.
    rewrite /= !atom_member_union atom_member_remove_full IHc andbF /=.
    by case: (atom_member _ lb || _); rewrite /= ?Hat.
  case Ev: (value_needs cv k eA) => [rd fl].
  rewrite /= !atom_member_union atom_member_remove_full IHc andbF (Hrd _ _ Ev).
  by case: (atom_member _ lb || _); rewrite /= ?Hat.
have Hnt : (forall x, fbody (b' x)) -> WellFormed.is_tail cW k = false.
  move=> Hb'; rewrite /WellFormed.is_tail; move: (HcW x1 (anon k)) (Hb' x1).
  by case: (b' x1) => [? ? ? | ?]; case: (cW (anon k)).
have Hends : (forall x, fbody (b' x)) ->
    ends_with_fold (S k) (cW (anon k)) = true.
  move=> Hb'; apply: (fbody_ends _ _ (b' x1) _ (Hb' x1) (HcW x1 (anon k))).
  by case: Hag' => _ Hlt p w I; exact: Hlt _ _ (or_intror I).
have Hnf : (forall x, fbody (b' x)) ->
    (forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0) ->
    occurs_value j k eW = false /\
    reads_around_inner_loop j (S k) (cW (anon k)) = false.
  move=> Hb' Hne; move: Hra; rewrite /reads_around_inner_loop.
  have Ee : forall ew, (forall a0 lo0 hi0 i0 bb0,
      ew <> AFold a0 lo0 hi0 i0 bb0) ->
      ends_with_fold k (ALet aW ew cW) = ends_with_fold (S k) (cW (anon k)).
    by case=> //= ? ? ? ? ? /(_ _ _ _ _ _ erefl).
  rewrite (Ee _ Hne).
  rewrite /= Hnt // Hends //= => /orb_false_iff [Ho Hr].
  by rewrite Ho Hr.
case: e Hb HeA HeW HeW1 Hop => //= [? ? | ? ? ? | ? ? | a1 lo hi [s | ? | ?] bi]
  //= Hb HeA HeW HeW1 Hop.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  by have [Ho Hr] := Hnf Hb Hne; exact: Hop.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  by have [Ho Hr] := Hnf Hb Hne; exact: Hop.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  by have [Ho Hr] := Hnf Hb Hne; exact: Hop.
(* the inner fold, the tail *)
case: Hb => _ [_ Hret]; clear Hop Hnf Hnt Hends.
case: eA HeA x1 Hid' Hag' Hty' => // aA' loA hiA iA biA
  [HloA [HhiA [HiA HbiA]]] x1 Hid' Hag' Hty'.
case: eW HeW Hra => // aW' loW hiW iW biW [HloW [HhiW [HiW HbiW]]] Hra.
case: eW1 HeW1 Ete => // aW1' loW1 hiW1 iW1 biW1
  [HloW1 [HhiW1 [HiW1 HbiW1]]] Ete.
case: iW1 HiW1 Ete => // w1 Hw1 Ete.
(* the typecheck of the inner fold *)
rewrite /= in Ete.
case Elh: (_ && _) Ete => // Ete.
case: (ty_eqb _ Real) Ete => // Ete.
case: (vty w1) Ete => [| | | n] // Ete.
case: (WellFormed.is_tail cW1 k) Ete => // Ete.
case Ev: (vid w1 =? vid sv)%nat Ete => // Ete.
have Ew1 : vid w1 = j by move/Nat.eqb_eq: Ev; rewrite Hsv.
case Hocc1: (occurs_anf (vid w1) (S (S k)) (biW1 (anon k) (anon (S k)))) Ete
  => Ete.
  by case: (varg w1) Ete => [[? ?] |].
(* the continuation returns the fold: it needs nothing *)
rewrite /=.
case Eb: (needs cv Replay (S k) (cA (let_binder k _))) => [ub lb].
have Elb : lb = [].
  move: Eb; have := HcA x1 (let_binder k (AFold aA' loA hiA iA biA)).
  by rewrite (Hret x1); case: (cA _) => [? ? ? | ?] //= _ [_ <-].
subst lb; case: (_ && _) => //=.
(* its body does not read j, the state of the outer loop *)
set vr := fold_varied k iA biA.
set xi := PV (AV k false) (anon k) dummy_tvar (VInt 0%Z) 0.
set ys := PV (AV (S k) vr) (anon (S k)) dummy_tvar (VInt 0%Z) 0.
have Hid2 : forall q, In q (ys :: xi :: G) -> aid (pa q) = vid (pw q).
  by move=> q [<- | [<- | Hq]] //; exact: Hid.
have Hag2 : agree ((ys, anon (S k)) :: (xi, anon k) :: G1)
    (gW (ys :: xi :: G)) (S (S k)).
  by apply: agree_cons => //; apply: agree_cons.
have Etr := (proj1 occurs_transfer) (bi xi ys) _ _ _ _ j (S (S k))
  (HbiW1 xi _ ys _) (HbiW xi _ ys _) Hag2.
have Hj2 : (j < S (S k))%nat by lia.
case Hn: (needs cv Replay (S (S k)) (biA _ _)) => [u l] /=.
have Hl : atom_member (AVar (AV j false)) l = false.
  case El: (atom_member _ l) => //.
  have := (proj1 (needs_occurs cv)) (bi xi ys) (ys :: xi :: G) _ _ Replay
    (S (S k)) j (HbiA xi _ ys _) (HbiW xi _ ys _) Hid2 Hj2.
  rewrite Hn /= El orbT -Etr -Ew1 Hocc1.
  by move=> /(_ erefl).
(* its bounds are integers *)
move/andP: Elh => [Elo Ehi].
rewrite !atom_member_union !atom_member_remove_full Hl !andbF.
rewrite (int_atom_not _ _ _ _ _ _ _ _ HloA HloW HloW1 Hag Hid Hty Elo).
by rewrite (int_atom_not _ _ _ _ _ _ _ _ HhiA HhiW HhiW1 Hag Hid Hty Ehi).
Qed.

(* The reverse sweep of the outer loop of a nest does not read its state:
   the state is not live, the loop does not record it. *)
Lemma fbody_state_dead L k (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
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
  state_live cv k initA bA = false.
Proof.
move=> Hfb HbA HbW HL _ HtB Hra.
rewrite /state_live /fold_binders atom_member_id /=.
set vr := fold_varied k initA bA.
set ix := PV (AV k false) (anon k) dummy_tvar (VInt 0%Z) 0.
set sx := PV (AV (S k) vr) (anon (S k)) dummy_tvar (VInt 0%Z) 0.
have Hag : agree (gW L) (gW L) k.
  split; first by move=> p w1 w2 /in_gW [_ ->] /in_gW [_ ->].
  by move=> p w [] /in_gW [I _]; exact: aids_below HL p I.
apply: (fbody_needs (bP ix sx) (Hfb ix sx) (sx :: ix :: L)
  ((sx, VInfo (S k) (Array z) None) :: (ix, VInfo k Integer None) :: gW L)
  _ _ _ (S (S k)) (S k) (option_map (amap pw) wP)
  (AVar (VInfo k Integer None)) (VInfo (S k) (Array z) None) (Array z)
  (HbA ix _ sx _) (HbW ix _ sx _) (HbW ix _ sx _)) => //.
- by apply: agree_cons => //; apply: agree_cons.
- by move=> q [<- | [<- | Hq]] //; case: (static_in _ _ _ HL Hq).
move=> p w [[_ <-] // | [[_ <-] /= | /in_gW [I ->] E]]; first lia.
by have [_ [Hk _]] := static_in _ _ _ HL I; lia.
Qed.

End NestSide.
