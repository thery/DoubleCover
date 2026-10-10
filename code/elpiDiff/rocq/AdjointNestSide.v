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
Lemma fbody_act b : fbody b -> act_body b.
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
by move=> Hq Hfb; apply: act_fold_gen Hq _ => x y; apply/fbody_act.
Qed.

(* Not varied, it leaves the tangent of its array as it was: zero. *)
Lemma owner_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> act_owner (AFold a loP hiP initP bP).
Proof.
by move=> Hq Hfb; apply: owner_fold_gen Hq _ => x y; apply/fbody_act.
Qed.

(* Outside loops, it updates its init in place: the reverse sweep does not
   read it, and the fold is varied when it is. *)
Lemma inplace_fold_nest a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, fbody (bP x y)) -> inplace_only cv (AFold a loP hiP initP bP).
Proof.
by move=> Hq _; exact: inplace_fold_gen.
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
