(* AdjointGoodRev.v — the reverse sweep of the adjoint code keeps the
   scoping discipline (AdjointGood.v): rev_value and adj, for every body and
   every value, by induction on the syntax. What the reverse code reads was
   computed by the forward code (the TBR set of needs), the adjoints it
   accumulates into are declared (the useful set), and the tapes it pops are
   declared (the records).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops
  TangentGood AdjointCorrect AdjointBranch AdjointGood AdjointGoodFwd.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section AGoodRev.
Variable cv : bool.

(* An atom whose variable is in scope, spelled. *)
Lemma spell_scope L k sc (aP : atom pv) :
  Forall (static_ok k) L ->
  (forall p, aP = AVar p -> In p L /\ In (stored p) sc) ->
  expr_ok sc (spell (amap pt aP)).
Proof.
move=> HL; case: aP => [p | |] H //=.
have [Hp Hs] := H p erefl.
by have [_ [_ [-> _]]] := static_in _ _ _ HL Hp.
Qed.

(* The adjoint of an atom, when it has one: the adjoint of its variable,
   varied. *)
Lemma bar_atom L k (aP : atom pv) ba :
  Forall (static_ok k) L ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  (forall p, aP = AVar p -> In p L) ->
  bar (amap pt aP) = Some ba ->
  exists p, aP = AVar p /\ In p L /\ avaried (pa p) = true /\
            ba = DVar (BarOf (stored p)).
Proof.
move=> HL Hbar; case: aP => [p | |] //= Hp.
have Hp' := Hp p erefl.
have [_ [_ [Hst _]]] := static_in _ _ _ HL Hp'.
rewrite (Hbar p Hp') Hst; case Ev: (avaried (pa p)) => // -[<-].
by exists p.
Qed.

Ltac arev_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in
  intros L k c wP pp vo tail eA eW eT te n ty sc wr HA HW HT Hs Hbar Hb Hw
    Hrd Hbo Htc Htail [j [Ej Hj]] Hst Hbn Hrt Hsl;
  destruct eA, eW, eT; simpl in HA, HW, HT; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
         end; subst.

Lemma agood_rev_op1 f (aP : atom pv) : agood_rev cv (AOp1 f aP).
Proof.
arev_intro.
rewrite /=; split=> // rest Hrest.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hr0 := Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw I.
case Hp1: (partial1 f2 (amap pt aP)) => [p |] //.
rewrite /contribution; case Eb: (bar (amap pt aP)) => [ba |] //=.
have [q [Eq [Hq [Hvq Eba]]]] := bar_atom L k aP ba HL Hbar H0 Eb.
subst aP ba.
have [_ [_ [Hst' _]]] := static_in _ _ _ HL Hq.
have Hrq : vreads cv k (AOp1 f2 (amap pa (AVar q))) q -> In (stored q) sc.
  by move=> H; exact: Hrd q Hq H.
have Hfq : vflows cv k (AOp1 f2 (amap pa (AVar q))) q.
  by rewrite /vflows /= Nat.eqb_refl.
have Htq : tbar (pt q) = true by rewrite Hbar.
apply: GoodIncrement => //; first exact: (proj1 Hbo q Hq Hfq Htq).
apply/expr_ok_allv; apply: allv_scale; last first.
  by move=> x [<- | []]; apply: Hw.
move: Hp1 Hrq.
destruct f2 as [| | | | | | z | s]; try destruct z;
  move=> //= [<-] Hrq x;
  rewrite /= ?Hst' ?app_nil_r /=; first [by case |
    case=> [<- | []]; apply: Hrq; rewrite /vreads /= Hvq /= Nat.eqb_refl //].
Qed.

(* A contribution to the adjoint of an operand: declared when the operand is
   varied, its partial derivative read from the scope. *)
Lemma good_contribution L k sc wr (aP : atom pv) pe x rest :
  Forall (static_ok k) L ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  (forall p, aP = AVar p -> In p L) ->
  (forall p, aP = AVar p -> avaried (pa p) = true ->
     In (BarOf (stored p)) wr) ->
  (forall p, aP = AVar p -> avaried (pa p) = true ->
     expr_ok sc (spell_partial pe)) ->
  In x sc -> good sc wr rest ->
  good sc wr (contribution W (amap pt aP) pe x ++ rest).
Proof.
move=> HL Hbar Ha Hbw Hpe Hx Hr; rewrite /contribution.
case Eb: (bar (amap pt aP)) => [ba |] //=.
have [q [Eq [Hq [Hvq Eba]]]] := bar_atom L k aP ba HL Hbar Ha Eb; subst.
apply: GoodIncrement => //; first exact: Hbw q erefl Hvq.
apply/expr_ok_allv; apply: allv_scale; last by move=> y [<- | []].
by apply/expr_ok_allv; exact: Hpe q erefl Hvq.
Qed.

Lemma agood_rev_op2 f (aP bP : atom pv) : agood_rev cv (AOp2 f aP bP).
Proof.
arev_intro.
rewrite /=; split=> // rest Hrest.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hr0 := Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw I.
have Hx : In (BarOf (DBound (j, j))) sc by apply: Hw.
have Hbw : forall aQ, (aQ = aP \/ aQ = bP) -> forall q, aQ = AVar q ->
    avaried (pa q) = true -> comparison f2 = false ->
    In (BarOf (stored q)) wr.
  move=> aQ HaQ q Eq Hvq Hcf.
  have Hq : In q L by case: HaQ => E; subst; auto.
  apply: (proj1 Hbo q Hq); last by rewrite Hbar.
  rewrite /vflows; cbn [value_needs]; rewrite Hcf.
  have Hin : In (amap pa aQ) [amap pa aP; amap pa bP].
    by case: HaQ => ->; [left | right; left].
  have Ea : amap pa aQ = AVar (pa q) by rewrite Eq.
  case: (partial2 f2 (amap pa aP) (amap pa bP)) => [[? ?] |]; cbn [snd];
    exact: (atom_member_atoms (pa q) _ _ Hin Ea).
have Hsp : forall aQ, (aQ = aP \/ aQ = bP) ->
    (forall q, aQ = AVar q -> vreads cv k (AOp2 f2 (amap pa aP) (amap pa bP)) q)
    -> expr_ok sc (spell (amap pt aQ)).
  move=> aQ HaQ Hv; apply: (spell_scope L k) => // q Eq.
  have Hq : In q L by case: HaQ => E; subst; auto.
  by split=> //; apply: Hrd q Hq (Hv q Eq).
case Ep: (partial2 f2 (amap pt aP) (amap pt bP)) => [[pe1 pe2] |] //.
have Hcf : comparison f2 = false by case: (f2) Ep.
rewrite -app_assoc.
have Hva : forall q, aP = AVar q -> avaried (pa q) = true ->
    varied (amap pa aP) = true by move=> q -> /=.
have Hvb : forall q, bP = AVar q -> avaried (pa q) = true ->
    varied (amap pa bP) = true by move=> q -> /=.
apply: (good_contribution L k) => //.
- by move=> q Eq Hvq; exact: (Hbw aP (or_introl erefl) q Eq Hvq Hcf).
- move=> q Eq Hvq; have Hv := Hva q Eq Hvq.
  destruct f2; rewrite /= in Ep; try discriminate; case: Ep => <- _ //=;
    (try split=> //); apply: (Hsp bP (or_intror erefl)) => r Er;
    by rewrite /vreads /= Hv /= atom_member_union Er /= Nat.eqb_refl.
apply: (good_contribution L k) => //.
- by move=> q Eq Hvq; exact: (Hbw bP (or_intror erefl) q Eq Hvq Hcf).
move=> q Eq Hvq; have Hv := Hvb q Eq Hvq.
destruct f2; rewrite /= in Ep; try discriminate; case: Ep => _ <- //=;
  repeat split=> //;
  first [apply: (Hsp aP (or_introl erefl)) | apply: (Hsp bP (or_intror erefl))]
  => r Er;
  by rewrite /vreads /= Hv /= ?atom_member_union Er /= Nat.eqb_refl
    ?orb_true_r.
Qed.

Lemma agood_rev_get (aP iP : atom pv) : agood_rev cv (AGet aP iP).
Proof.
arev_intro.
rewrite /=; split=> // rest Hrest.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hr0 := Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw I.
have HaL : forall p, aP = AVar p -> In p L by [].
have HiL : forall p, iP = AVar p -> In p L by [].
case Eb: (bar (amap pt aP)) => [ba |] //=.
have [q [Eq [Hq [Hvq Eba]]]] := bar_atom L k aP ba HL Hbar HaL Eb.
subst ba.
have Hi : expr_ok sc (spell (amap pt iP)).
  apply: (spell_scope L k) => // r Er; split; first exact: HiL.
  by apply: Hrd (HiL r Er) _; rewrite /vreads /= Er /= Nat.eqb_refl.
have Hfq : vflows cv k (AGet (amap pa aP) (amap pa iP)) q.
  by rewrite /vflows /= Eq /= Nat.eqb_refl.
have Hlhs : lhs_ok sc wr
    (DAt (DVar (BarOf (stored q))) (spell (amap pt iP))).
  split=> //; apply: (proj1 Hbo q Hq Hfq).
  by rewrite Hbar.
have Hn : expr_ok sc (DVar (BarOf (DBound (j, j)))) by apply: Hw.
exact: GoodIncrement.
Qed.

Lemma agood_rev_set (aP iP vP : atom pv) : agood_rev cv (ASet aP iP vP).
Proof.
arev_intro.
rewrite /=; split=> // rest Hrest.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hr0 := Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw I.
have HiL : forall p, iP = AVar p -> In p L by [].
have HvL : forall p, vP = AVar p -> In p L by [].
have Hi : expr_ok sc (spell (amap pt iP)).
  apply: (spell_scope L k) => // r Er; split; first exact: HiL.
  by apply: Hrd (HiL r Er) _; rewrite /vreads /= Er /= Nat.eqb_refl.
have Hel : lhs_ok sc wr (DAt (DVar (BarOf (DBound (j, j))))
                           (spell (amap pt iP))) by [].
have Hel' : expr_ok sc (DAt (DVar (BarOf (DBound (j, j))))
                           (spell (amap pt iP))) by split=> //; apply: Hw.
case Eb: (bar (amap pt vP)) => [bv |] //=.
  have [q [Eq [Hq [Hvq Ebv]]]] := bar_atom L k vP bv HL Hbar HvL Eb.
  subst bv.
  have Hfq : vflows cv k (ASet (amap pa aP) (amap pa iP) (amap pa vP)) q.
    by rewrite /vflows /= atom_member_union Eq /= Nat.eqb_refl orb_true_r.
  apply: GoodIncrement => //.
    by apply: (proj1 Hbo q Hq Hfq); rewrite Hbar.
  by apply: GoodAssign.
by apply: GoodAssign.
Qed.

(* A body that returns an atom: the value given back, at the top of
   adjoint-value; the seed accumulated into the adjoint of the atom. *)
Lemma agood_body_ret (aP : atom pv) : agood_body cv (ARet aP).
Proof.
move=> L k c wP pp m vo [? ? ? | aA] [? ? ? | aW] [? ? ? | aT] //= ty se
  HA HW HT Hs _ Hbar Hcv _ _ _.
case/atom_graph: HT => ET HT; case/atom_graph: HA => EA HA.
case/atom_graph: HW => EW _; subst aT aA aW.
have HL := s_static _ _ _ _ _ _ _ Hs.
split=> //; exists (fun _ => False) => sc wr Hsc _ Hvo.
have [Hb [Hw [Hr _]]] := Hsc.
have Hx : m = Forward -> vo <> None -> expr_ok sc (spell (amap pt aP)).
  move=> Hm Hv; apply: (spell_scope L k) => // p E; split; first exact: HA.
  apply: Hr (HA p E) _; rewrite /tbr /= Hm (Hcv Hm Hv) /= E /=.
  by rewrite Nat.eqb_refl.
move=> rest Hrest.
have Hpost : forall sc1, (forall x, In x sc1 -> In x sc \/ x = ResultVar) ->
    fwd_post (fun _ => False) c c sc sc1.
  move=> sc1 H y /H [Hy | ->]; [by left | by right; right; left].
(* the reverse sweep: the seed accumulated into the adjoint of the atom *)
have Hrv : forall sc1 wr1 sc2 wr2,
    rscope (fun _ => False) c c sc1 wr1 sc2 wr2 ->
    bars_ok L (useful cv m k (ARet (amap pa aP))) wP pp wr2 ->
    tape_rev wP pp false wr2 -> expr_ok sc2 se ->
    good_k sc2 wr2 c
      match tof (amap pt aP) with
      | Real => match bar (amap pt aP) with
                | Some bx => [DIncrement bx se] | None => [] end
      | _ => [] end (fun=> (fun=> True)).
  move=> sc1 wr1 sc2 wr2 [_ [_ [Hw2 [Hb2 _]]]] Hbo _ Hse rest' Hrest'.
  have Hr0 : good sc2 wr2 rest'.
    exact: Hrest' sc2 wr2 (incl_refl _) (incl_refl _) Hb2 Hw2 I.
  case: (tof _) => //; case Eb: (bar (amap pt aP)) => [bx |] //=.
  have [q [Eq [Hq [Hvq Ebx]]]] := bar_atom L k aP bx HL Hbar HA Eb.
  subst bx; apply: GoodIncrement => //.
  apply: (proj1 Hbo q Hq); last by rewrite Hbar.
  by rewrite /useful /= Eq; case: (sweep_eqb m Forward && cv) => /=;
    rewrite Nat.eqb_refl.
have Hq0 : forall sc1 wr1,
    (forall x, In x sc1 -> In x sc \/ x = ResultVar) ->
    (m = Forward -> forall t, vo = Some (AReturns t) -> In ResultVar sc1) ->
    fwd_post (fun _ => False) c c sc sc1 /\
    (m = Forward -> forall t, vo = Some (AReturns t) -> In ResultVar sc1) /\
    (forall sc2 wr2, rscope (fun _ => False) c c sc1 wr1 sc2 wr2 ->
      bars_ok L (useful cv m k (ARet (amap pa aP))) wP pp wr2 ->
      tape_rev wP pp false wr2 -> expr_ok sc2 se ->
      good_k sc2 wr2 c
        match tof (amap pt aP) with
        | Real => match bar (amap pt aP) with
                  | Some bx => [DIncrement bx se] | None => [] end
        | _ => [] end (fun=> (fun=> True))).
  move=> sc1 wr1 H HR.
  by split; [exact: Hpost | split; [exact: HR | exact: Hrv]].
(* the forward sweep: the value given back, at the top of adjoint-value *)
have Hr0 : (m = Forward -> forall t, vo = Some (AReturns t) ->
              In ResultVar sc) -> good sc wr rest.
  move=> HR.
  apply: Hrest; [exact: incl_refl | exact: incl_refl | exact: Hb | exact: Hw |].
  by apply: Hq0 => // y Hy; left.
case Em: (sweep_eqb m Forward) => /=; last first.
  by apply: Hr0 => Hm; rewrite Hm in Em.
have Hmf : m = Forward by case: (m) Em.
destruct vo as [[t | y] |]; rewrite /=; last by apply: Hr0.
  have [Hnr _] := Hvo Hmf.
  apply: GoodConstant => //; [exact: Hx | exact: Hnr t erefl |].
  apply: Hrest; [by move=> z Hz; right | exact: incl_refl | | |].
  - by constructor=> //; split.
  - by move=> z Hz; right; apply: Hw.
  apply: Hq0 => [z [<- | Hz] | _ t' _]; [right | left | left] => //.
have {}Hr0 : good sc wr rest by apply: Hr0.
case: (tof y) => //; case: (role_of W y) => [[] |] //=.
have [_ Hwy] := Hvo Hmf.
by apply: GoodAssign => //; [exact: Hwy y erefl | exact: Hx].
Qed.

(* ---------------------------------------------------------------------------
   Scopes and numbers. *)

Lemma good_k_mono sc wr c c' ss (Q : list (dvar W) -> list (dvar W) -> Prop) :
  good_k sc wr c ss Q -> (c <= c')%nat -> good_k sc wr c' ss Q.
Proof.
move=> Hg Hc rest Hr; apply: Hg => sc' wr' I1 I2 Hb Hw HQ.
apply: Hr => //; apply: (Forall_impl _ _ Hb) => x [H1 H2]; split=> //.
exact: below_mono H1 Hc.
Qed.

Lemma below_dnum c x :
  below c x <-> (forall j, dnum x = Some j -> (j < c)%nat).
Proof.
elim: x => [[i i'] | v IH | v IH | v IH |] /=; try exact: IH.
  by split=> [H j [<-] | H]; [| apply: H].
by split.
Qed.

(* The scope of the reverse sweep of a let, below the end of its rest, when
   the variables the forward sweep defines are numbered below it. *)
Lemma rscope_below (F : nat -> Prop) c c1 c3 sc :
  (c <= c1)%nat -> (forall j, F j -> (j < c1)%nat) ->
  Forall (fun x => below c3 x /\ consistent x) sc ->
  (forall x, In x sc -> ~ rev_new F c c3 x) ->
  Forall (fun x => below c1 x /\ consistent x) sc.
Proof.
move=> Hc HF /Forall_forall Hb Hn; apply/Forall_forall => x Hx.
have [Hb3 Hcx] := Hb x Hx; split=> //.
apply/below_dnum => j Ej.
have Hj3 := proj1 (below_dnum c3 x) Hb3 j Ej.
case: (Nat.lt_ge_cases j c1) => // Hj1; exfalso; apply: (Hn x Hx).
exists j; split; first lia.
split=> //; case Eb: (is_barv x); first by left.
by right=> /HF; lia.
Qed.

Lemma bar_declaration_array z (n : dvar W) :
  bar_declaration W (Array z) n = [].
Proof. by []. Qed.

Lemma fold_slive_records k (eA : value avar bare) :
  fold_slive cv k eA = true -> records cv k eA = true.
Proof.
case: eA => // ? ? ? init b /=; rewrite /state_live /fold_binders.
by move=> ->.
Qed.

(* ---------------------------------------------------------------------------
   A let: the forward sweep of its value (when computed), then of the rest;
   the reverse sweep of the rest, then of its value (when active), after the
   declaration of its adjoint. *)

Lemma good_k_weaken sc wr c c' ss
  (Q Q' : list (dvar W) -> list (dvar W) -> Prop) :
  good_k sc wr c ss Q -> (c <= c')%nat ->
  (forall sc' wr', incl sc sc' -> incl wr wr' ->
     Forall (fun x => below c x /\ consistent x) sc' -> incl wr' sc' ->
     Q sc' wr' -> Q' sc' wr') ->
  good_k sc wr c' ss Q'.
Proof.
move=> Hg Hc HQ rest Hr; apply: Hg => sc' wr' I1 I2 Hb Hw Hq.
apply: Hr => //; last exact: HQ.
apply: (Forall_impl _ _ Hb) => x [H1 H2]; split=> //.
exact: below_mono H1 Hc.
Qed.

Lemma good_k_good sc wr c ss (Q : list (dvar W) -> list (dvar W) -> Prop) :
  good_k sc wr c ss Q -> good sc wr ss.
Proof. by move=> Hg; rewrite -[ss]app_nil_r; apply: Hg => *; constructor. Qed.

Lemma bars_ok_mono L (use : pv -> Prop) wP pp wr wr' :
  bars_ok L use wP pp wr -> incl wr wr' -> bars_ok L use wP pp wr'.
Proof.
move=> [B1 B2] I; split; first by move=> p Hp Hu Ht; apply/I/B1.
by move=> o Ho; have [B3 B4] := B2 o Ho; split; apply: I.
Qed.

(* A fold whose value is not stored in place is a scalar fold, at the
   top. *)
Lemma fold_top L k wP pp tail (eP : value pv bare) eA eW te :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW =
    (te, Ok) ->
  storage wP tail eP = None -> fold_slive cv k eA = true -> pp = PTop.
Proof.
move=> HA HW Htc Hs Hsl.
case: eA HA Hsl => // ? ? ? ? ? HA _.
case: eP HA HW Htc Hs => // an lo hi i b HA.
case: eW => // ? lo' hi' i' b' [_ [_ [Hi _]]] Htc Hs.
case Epp: pp Htc => [| | | ix sx] //= Htc; exfalso; clear HA; move: Htc;
  case: (_ && _) => //; case: (ty_eqb _ _) => //;
  case: i' Hi => [w | z | z] //= Hi; case: i Hi Hs => //= p /in_gW [_ <-] /=;
  intros;
  repeat match goal with H : context[vty ?w] |- _ => revert H end;
  by match goal with |- context[vty ?w] => case: (vty w) end.
Qed.

(* The value given back at the top of adjoint-value. *)
Lemma good_value_output sc wr vo (x : atom (tvar W)) rest :
  vo_scope Forward vo sc wr -> expr_ok sc (spell x) ->
  ((forall t, vo = Some (AReturns t) -> False) -> good sc wr rest) ->
  good (ResultVar :: sc) wr rest ->
  good sc wr (value_output W vo x ++ rest).
Proof.
move=> Hvo Hx Hr Hr'; case: vo Hvo Hr => [[t | y] |] Hvo Hr /=.
- by apply: GoodConstant => //; case: (Hvo erefl) => /(_ t erefl).
- have {}Hr : good sc wr rest by apply: Hr.
  case: (tof y) => //; case: (role_of W y) => [[] |] //=.
  by apply: GoodAssign => //; case: (Hvo erefl) => _ /(_ y erefl).
by apply: Hr.
Qed.

Lemma agood_body_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  agood_value cv eP -> agood_rev cv eP -> (forall x, agood_body cv (cP x)) ->
  agood_body cv (ALet a eP cP).
Proof.
move=> IHf IHr IHb L k c wP pp m vo bA bW bT ty se HA HW HT Hs Hroa
  Hbar Hcv Htc Hmf Hmr.
destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |];
  rewrite /= in HA HW HT; try contradiction.
case: HA => HeA HcA; case: HW => HeW HcW; case: HT => HeT HcT.
rewrite /= in Htc; move: Htc.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
             (WellFormed.is_tail cW k) k eW) => [te d0].
case: d0 Hte => [| msg] Hte /= Htc //.
cbn [annotate_body_t].
case Hneeds: (needs cv m (S k) (cA (let_binder k eA))) => [u l].
set vr := varied_value k eA; set vt := annotate_value_t cv k eA.
set rest := annotate_body_t cv m (S k) (cA (let_binder k eA)).
set ac := vr && atom_member (AVar (let_binder k eA)) u.
set cp := atom_member (AVar (let_binder k eA)) l ||
  sweep_eqb m Forward && records cv k eA.
cbn [rebuild]; rewrite adj_let; cbv [let_ann].
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
match goal with |- context [with_storage _ _ _ ?K] => set Kf := K end.
have Hwr : forall a0, wP = Some a0 -> exists y, a0 = AVar y /\ In y L.
  move=> a0 E; have [y [-> [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ E.
  by exists y.
have [n [rec [c0 [Hopen Hn]]]] := open_with_storage_v L k wP eP eT vt
  (fun v0 => rebuild _ (cT v0) rest) Kf c HeT HL Hwr.
rewrite Hopen.
have Htid : forall p, In p L ->
    (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat.
  move=> p Hp.
  by have [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]] := static_in _ _ _ HL Hp.
rewrite -(is_tail_transfer L k cP cW cT rest HcW HcT Htid) in Hn.
set tail := WellFormed.is_tail cW k in Hte Hn *.
rewrite /Kf open_pairs_sbind.
case Hb: (open_pairs (adj W (option_map (amap pt) wP) vo m
  (rebuild (tvar W) (cT (open_let te n vr rec)) rest) se) c0)
  => [[fb rb] c1].
rewrite open_pairs_sbind.
case Hfe: (open_pairs (if cp then fwd_value W (option_map (amap pt) wP) m
  (rebuild_value (tvar W) eT vt) te n rec else Done []) c1) => [fe c2].
rewrite open_pairs_sbind.
case Hre: (open_pairs (if ac then rev_value W (option_map (amap pt) wP) vo
  (rebuild_value (tvar W) eT vt) te n else Done []) c2) => [re c3].
cbn [open_pairs].
have Hc01 : (c0 <= c1)%nat.
  by rewrite -[c1]/(snd (fb, rb, c1)) -Hb; exact: open_pairs_mono.
have Hc12 : (c1 <= c2)%nat.
  by rewrite -[c2]/(snd (fe, c2)) -Hfe; exact: open_pairs_mono.
have Hc23 : (c2 <= c3)%nat.
  by rewrite -[c3]/(snd (re, c3)) -Hre; exact: open_pairs_mono.
have Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by move=> p H; rewrite /live_value /live_anf /= in H *; rewrite H.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Hs0 : sctx L k c wP pp (live_value k eW) ty.
  exact: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e (le_n c)).
have Hpk : forall p, In p L -> (aid (pa p) < k)%nat.
  exact: aids_below.
(* the number of n *)
have Hnum : exists j, n = DBound (j, j) /\ (j < c0)%nat /\ (c <= c0)%nat /\
    match storage wP tail eP return Prop with
    | Some _ => True | None => j = c end.
  case Es: (storage wP tail eP) Hn => [m0 |] [-> [-> _]]; last first.
    by exists c; repeat split; lia.
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [_ [o [Ho' Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em; subst m0.
  exists (pn o); split=> //.
  have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho'); lia.
have [j [Ej [Hj0 [Hc0 Hjs]]]] := Hnum.
(* the rest of the body, for a fresh variable *)
set xf := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec)
            (default_dual te) c.
have [Fb HFb] : exists Fb : nat -> Prop, storage wP tail eP = None ->
    forall sc wr,
    fscope (xf :: L) c0 wP pp (tbr cv m (S k) (cA (pa xf))) sc wr ->
    tape_fwd wP pp m (records_in cv (S k) (cA (pa xf))) sc wr ->
    vo_scope m vo sc wr ->
    good_k sc wr c1 fb (fun sc1 wr1 =>
      fwd_post Fb c0 c1 sc sc1 /\
      (m = Forward -> forall t, vo = Some (AReturns t) ->
         In ResultVar sc1) /\
      forall sc2 wr2, rscope Fb c0 c1 sc1 wr1 sc2 wr2 ->
        bars_ok (xf :: L) (useful cv m (S k) (cA (pa xf))) wP pp wr2 ->
        tape_rev wP pp (records_in cv (S k) (cA (pa xf))) wr2 ->
        expr_ok sc2 se ->
        good_k sc2 wr2 c1 rb (fun _ _ => True)).
  case Es: (storage wP tail eP); first by exists (fun _ => False).
  move: Hn; rewrite Es => -[En [Ec0 Erec]]; subst c0.
  have Hx : aid (pa xf) = k by [].
  have HxL : ~ In xf L := fresh_notin L k xf (aids_below L k HL) Hx.
  have Hvid : forall p, In p L -> (vid (pw p) < k)%nat.
    by move=> p Hp; have [_ [H _]] := static_in _ _ _ HL Hp.
  have Hlive_c : forall p, In p L ->
      live_anf (S k) (cW (VInfo k te None)) p -> live_anf k (ALet aW eW cW) p.
    rewrite /live_anf => p Hp H /=.
    rewrite (live_cont L k cP cW xf (VInfo k te None) _ HcW HL Hx erefl) in H.
    by rewrite H orb_true_r.
  set cW' := cW (VInfo k te None).
  have Hxs : static_ok (S k) xf.
    have [D1 D2] := default_dual_ok te.
    repeat split; rewrite /=; auto; try lia; try discriminate.
    move=> Hv.
    exact: (varied_real_or_array _ _ _ _ _ _ _ _ _ HeA HeW HL Hte Hv).
  have Hs' : sctx (xf :: L) (S k) (S c) wP pp (live_anf (S k) cW') ty.
    constructor.
    - constructor=> //; apply: (Forall_impl _ _ HL) => p Hp.
      by apply: (static_mono k _ p Hp); lia.
    - move=> p q [Ep | Hp] [Eq | Hq] E; try subst p; try subst q; try done.
      + by have := Hvid _ Hq; rewrite /= in E; lia.
      + by have := Hvid _ Hp; rewrite /= in E; lia.
      exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
    - move=> p [<- /= | Hp]; first lia.
      by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
    - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
      by exists y; split=> //; split; [right |].
    - have Hp := s_place _ _ _ _ _ _ _ Hs; destruct pp; simpl in Hp |- *;
        auto.
      by case: Hp => A [B C]; split; [right | split; [right |]].
    - move=> o p Ho' [<- | Hp] Ep.
        have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho').
        by rewrite /= in Ep; lia.
      case: (s_owner _ _ _ _ _ _ _ Hs o p Ho' Hp Ep) => [H | H]; first by left.
      by right=> Hl; apply: H; apply: Hlive_c.
    - move=> p o [<- | Hp] Lp Ha Hg Ho'.
        have [_ [o' [_ Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _
                                   Hs HeW Hte Htail_ty (or_intror Ha).
        by rewrite Es in Es'.
      exact: (s_arrays _ _ _ _ _ _ _ Hs p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho').
    - exact: (s_ty _ _ _ _ _ _ _ Hs).
    move=> y Hpp Hw' Ha.
    have [y' [E [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ Hw'.
    case: E => Ey; subst y'.
    have [T1 T2] := s_top _ _ _ _ _ _ _ Hs y Hpp Hw' Ha.
    by split=> // Ly; apply: T2; apply: Hlive_c.
  have Hbarx : forall p, In p (xf :: L) -> tbar (pt p) = avaried (pa p).
    by move=> p [<- | Hp] //; apply: Hbar.
  have IH := IHb xf (xf :: L) (S k) (S c) wP pp m vo (cA (pa xf)) cW'
    (cT (pt xf)) ty se (HcA xf _) (HcW xf _) (HcT xf _) Hs' Hroa Hbarx Hcv
    Htc Hmf Hmr.
  rewrite /xf in IH; cbn [pt pa] in IH; rewrite -/rest Hb in IH.
  by case: IH => _ [F HF]; exists F => _.
set Flet := fun j => storage wP tail eP = None /\
  (j = c \/ (c0 <= j < c1 /\ Fb j))%nat.
split; first lia.
exists Flet => sc wr Hsc Htp Hvo.
have [Hbs [Hws [Hrs Hos]]] := Hsc.
(* a recorded storage is the state of an in-place loop, with its tape *)
have Hrec : rec = true ->
    ~ not_in_loop pp /\ (sweep_eqb m Forward = true -> In (TapeOf n) wr).
  case Es: (storage wP tail eP) Hn => [m0 |] Hn; last by case: Hn => _ [_ ->].
  case: Hn => En [_ [q [Hq [Eq [Er Hv]]]]] Erec.
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [_ [o [Ho' Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em0.
  have Eqo : stored q = stored o by rewrite Eq Em0.
  have Eq' := stor_owner _ _ _ _ _ _ _ _ _ _ _ _ Hs0 HeW Hte Hq Eqo Ho' Hv.
  subst q; have [T1 T2] := Htp o Ho'.
  have Hl : ~ not_in_loop pp.
    move=> Hl; have [_ [_ Hf]] := T1 Hl.
    by rewrite Hf in Er; rewrite Er in Erec.
  split=> // Hm; have [_ T3] := T2 Hl; rewrite En Em0; apply: T3.
  by rewrite Hm -Er Erec.
(* the reads of the value, when computed *)
have Hcp_reads : cp = true -> forall p, In p L -> live_value k eW p ->
    In (stored p) sc.
  move=> Ecp p Hp Hl; apply: (Hrs p Hp).
  apply: (tbr_let_atoms cv m k aA eA cA p).
    by rewrite Hneeds.
  exact: (live_vatoms _ _ _ _ _ p HeA HeW HL Hp Hl).
have Hst : match storage wP tail eP return Prop with
           | Some m0 => n = m0
           | None => ~ In n sc /\ ~ In (TapeOf n) sc
           end.
  case: (storage wP tail eP) Hn Hjs => [m0 | ] Hn Hjs; first by case: Hn.
  subst j; rewrite Ej.
  by split=> I; move/Forall_forall: Hbs => /(_ _ I) [Hbl _];
    rewrite /= in Hbl; lia.
(* the forward sweep of the value, when computed *)
set Qe := fun sc' wr' : list (dvar W) =>
  (cp = true -> In n sc') /\
  (forall x, In x sc' -> In x sc \/ x = n \/ x = TapeOf n) /\
  (sweep_eqb m Forward && records cv k eA = true -> not_in_loop pp ->
   storage wP tail eP <> None -> In (TapeOf n) wr') /\
  (sweep_eqb m Forward && fold_slive cv k eA = true ->
   storage wP tail eP = None -> In n wr' /\ In (TapeOf n) wr').
have Hfe_k : good_k sc wr c2 fe Qe.
  case Ecp: cp Hfe => Hfe; last first.
    case: Hfe => <- <-; apply: good_k_nil => //.
      apply: (Forall_impl _ _ Hbs) => x [H1 H2]; split=> //.
      by apply: (below_mono c); [exact: H1 | lia].
    rewrite /Qe Ecp; split=> //.
    split; first by move=> x Hx; left.
    have Hnr : sweep_eqb m Forward && records cv k eA = false.
      by move: Ecp; rewrite /cp => /orb_false_iff [].
    split; first by rewrite Hnr.
    case Hsl: (sweep_eqb m Forward && fold_slive cv k eA) => //.
    move/andP: Hsl => [Hm /fold_slive_records Hr0].
    by rewrite Hm Hr0 in Hnr.
  have Hsc1 : fscope L c1 wP pp (live_value k eW) sc wr.
    split.
      apply: (Forall_impl _ _ Hbs) => x [H1 H2]; split=> //.
      by apply: (below_mono c); [exact: H1 | lia].
    by split=> //; split=> // p Hp Hl; apply: Hcp_reads.
  have Htp1 : tape_fwd wP pp m (records cv k eA) sc wr.
    by apply: (tape_fwd_mono _ _ _ _ _ _ _ Htp); rewrite /= => ->.
  have Hj1 : exists j0, n = DBound (j0, j0) /\ (j0 < c1)%nat.
    by exists j; split=> //; lia.
  have Hcc1 : (c <= c1)%nat by lia.
  have IH0 := IHf L k c1 wP pp m tail eA eW eT te n rec ty sc wr HeA HeW HeT
    (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hcc1)
    Hsc1 Htp1 Hte Htail_ty Hj1 Hst Hrec.
  cbv zeta in IH0; rewrite -/vt Hfe in IH0.
  case: IH0 => _ Hg; move=> rest' Hrest'.
  apply: Hg => sc' wr' I1 I2 Hb' Hw' [Q1 [Q2 [Q3 Q4]]].
  by apply: Hrest' => //; split=> // _.
have Hcc2 : (c <= c2)%nat by lia.
have Hbars : forall wr2,
    bars_ok L (useful cv m k (ALet aA eA cA)) wP pp wr2 ->
    ac = true -> bars_ok L (vflows cv k eA) wP pp wr2.
  move=> wr2 [B1 B2] Eac; split=> // p Hp Hf; apply: B1 => //.
  apply: (useful_let_flows cv m k aA eA cA p) => //.
  by move: Eac; rewrite /ac Hneeds.
have Hreads : forall sc2, incl sc sc2 -> ac = true ->
    forall p, In p L -> vreads cv k eA p -> In (stored p) sc2.
  move=> sc2 I Eac p Hp Hv; apply/I/(Hrs p Hp).
  apply: (tbr_let_reads cv m k aA eA cA p) => //.
  by move: Eac; rewrite /ac Hneeds.
case Es: (storage wP tail eP) Hn Hst Hjs => [m0 |] Hn Hst Hjs.
  (* stored in place: the rest only returns the variable *)
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [Ht [o [Ho' Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em0.
  case: Hn => En [Ec0 _]; subst m0 c0.
  have Harr := inplace_array _ _ _ _ _ _ _ _ HeW Hte Hsn.
  set x := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec)
             (default_dual te) (pn o).
  have Hx : aid (pa x) = k by [].
  have HxL : ~ In x L := fresh_notin L k x (aids_below L k HL) Hx.
  have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
  have ET : cT (pt x) = ARet (AVar (pt x)).
    move: (HcT x (pt x)); rewrite Hcx.
    case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gT: I => I _.
  have EA : cA (pa x) = ARet (AVar (pa x)).
    move: (HcA x (pa x)); rewrite Hcx.
    case: (cA (pa x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => <-.
    by case/in_gA: I => I _; case: HxL.
  rewrite /= in ET EA.
  rewrite /rest EA in Hb; cbn [annotate_body_t rebuild] in Hb.
  rewrite ET in Hb; cbn [rebuild adj open_pairs] in Hb.
  destruct te as [| | | z]; try by case: Harr.
  case: Hb => Efb Erb Ec1; subst fb rb c1.
  have Hno : n = stored o by [].
  have Hnw : In n wr by rewrite Hno; apply: Hos.
  apply: (good_k_app sc wr c2 c3 fe _ Qe _ Hfe_k).
  move=> sc_e wr_e I1 I2 Hb_e Hw_e [Q1 [Q2 [Q3 Q4]]] rs Hrs0.
  have Hb_e3 : Forall (fun y => below c3 y /\ consistent y) sc_e.
    apply: (Forall_impl _ _ Hb_e) => y [H1 H2]; split=> //.
    exact: below_mono H1 Hc23.
  (* the reverse sweep of the value, from any extension of the scope *)
  have Hrv : forall sc2 wr2,
      rscope Flet c c3 sc_e wr_e sc2 wr2 ->
      bars_ok L (useful cv m k (ALet aA eA cA)) wP pp wr2 ->
      tape_rev wP pp (records_in cv k (ALet aA eA cA)) wr2 ->
      good_k sc2 wr2 c3 re (fun _ _ => True).
    move=> sc2 wr2 [I3 [I4 [Hw2 [Hb2 Hnr]]]] Hbol Htr.
    case Eac: ac Hre => Hre; last first.
      by move: Hre => /= [<- Ec]; subst c3; apply: good_k_nil.
    have HF2 : forall j0, Flet j0 -> (j0 < c2)%nat.
      by move=> j0 [E _]; rewrite Es in E.
    have Hb2' := rscope_below Flet c c2 c3 sc2 Hcc2 HF2 Hb2 Hnr.
    have Hj2 : exists j0, n = DBound (j0, j0) /\ (j0 < c2)%nat.
      by exists j; split=> //; lia.
    have Hbn : In (BarOf n) wr2.
      by rewrite Hno; exact: (proj2 (proj2 Hbol o Ho')).
    have Hrt : records cv k eA = true -> storage wP tail eP <> None ->
        In (TapeOf n) wr2.
      move=> Hr0 _.
      case: (not_in_loop_dec pp) => Hl; last first.
        rewrite Hno; apply: (Htr o Ho' Hl).
        by rewrite /= Hr0.
      have Hmf' : m = Forward.
        destruct m => //; exfalso; apply: (Hmr erefl).
        by destruct pp; rewrite /= in Hl Ho'.
      by apply: I4; apply: Q3 => //; rewrite Hmf' /= Hr0.
    have Hsl : fold_slive cv k eA = true -> In n wr2 /\ In (TapeOf n) wr2.
      move=> /fold_slive_records Hr0; split; last exact: Hrt.
      by rewrite Hno; apply: (proj1 (proj2 Hbol o Ho')).
    have Hst' : match storage wP tail eP return Prop with
                | Some m0 => n = m0 | None => True end by rewrite Es.
    have I13 : incl sc sc2 by move=> y H; apply/I3/I1.
    have IH0 := IHr L k c2 wP pp vo tail eA eW eT (Array z) n ty sc2 wr2
      HeA HeW HeT (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hcc2) Hbar Hb2'
      Hw2 (Hreads sc2 I13 Eac)
      (Hbars wr2 Hbol Eac) Hte Htail_ty Hj2 Hst' Hbn Hrt Hsl.
    cbv zeta in IH0; rewrite -/vt Hre in IH0.
    exact: (proj2 IH0).
  have Hql : forall sc1 wr1, incl sc_e sc1 -> incl wr_e wr1 ->
      (forall y, In y sc1 -> In y sc_e \/ y = ResultVar) ->
      (m = Forward -> forall t, vo = Some (AReturns t) ->
         In ResultVar sc1) ->
      fwd_post Flet c c3 sc sc1 /\
      (m = Forward -> forall t, vo = Some (AReturns t) ->
         In ResultVar sc1) /\
      (forall sc2 wr2, rscope Flet c c3 sc1 wr1 sc2 wr2 ->
        bars_ok L (useful cv m k (ALet aA eA cA)) wP pp wr2 ->
        tape_rev wP pp (records_in cv k (ALet aA eA cA)) wr2 ->
        expr_ok sc2 se ->
        good_k sc2 wr2 c3
          ((if ac then bar_declaration W (Array z) n else []) ++ [] ++ re)
          (fun _ _ => True)).
    move=> sc1 wr1 J1 J2 Hy HR; split.
      move=> y /Hy [/Q2 [Hy' | [-> | ->]] | ->].
      - by left.
      - by left; apply: Hws.
      - by right; right; right; exists j; rewrite Ej.
      by right; right; left.
    split; first exact: HR.
    move=> sc2 wr2 [I3 [I4 [Hw2 [Hb2 Hnr]]]] Hbol Htr _.
    have Hbd : (if ac then bar_declaration W (Array z) n else []) = [].
      by case: (ac).
    rewrite Hbd /=.
    have Hrs2 : rscope Flet c c3 sc_e wr_e sc2 wr2.
      split; first by move=> y H; apply/I3/J1.
      split; first by move=> y H; apply/I4/J2.
      by split.
    exact: Hrv.
  case Em: (sweep_eqb m Forward) => /=; last first.
    apply: Hrs0; [exact: incl_refl | exact: incl_refl | exact: Hb_e3 |
                  exact: Hw_e |].
    apply: Hql => //; first by move=> y Hy; left.
    by move=> Hm; rewrite Hm in Em.
  have Hmf' : m = Forward by case: (m) Em.
  apply: good_value_output.
  - move=> _; have [V1 V2] := Hvo Hmf'; split.
      move=> t Evo /Q2 [H | [E | E]]; first exact: (V1 t Evo H).
        by rewrite Ej in E.
      by rewrite Ej in E.
    by move=> y Hy; apply/I2/V2.
  - by rewrite /=; apply/I1/Hws.
  - move=> Hnr.
    apply: Hrs0; [exact: incl_refl | exact: incl_refl | exact: Hb_e3 |
                  exact: Hw_e |].
    apply: Hql => //; first by move=> y Hy; left.
    by move=> _ t Evo; case: (Hnr t Evo).
  apply: Hrs0; [by move=> y H; right | exact: incl_refl | | |].
  - by constructor=> //; split.
  - by move=> y H; right; apply: Hw_e.
  apply: Hql.
  - by move=> y H; right.
  - exact: incl_refl.
  - by move=> y [<- | H]; [right | left].
  by move=> _ t _; left.
(* a fresh variable: the forward sweep of the value, then of the rest *)
case: Hn => En [Ec0 Erec]; subst j c0 rec.
have Hna : ~ is_array te.
  move=> Ha.
  have [_ [o [_ Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_intror Ha).
  by rewrite Es in Es'.
have Hown_c : forall o, owner wP pp = Some o -> (pn o < c)%nat.
  move=> o Ho.
  exact: (s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho)).
apply: (good_k_app sc wr c2 c3 fe fb Qe _ Hfe_k).
move=> sc_e wr_e I1 I2 Hb_e Hw_e [Q1 [Q2 [Q3 Q4]]].
have Hb_e0 : Forall (fun x => below (S c) x /\ consistent x) sc_e.
  apply/Forall_forall => x Hx.
  have [_ Hcx] := proj1 (Forall_forall _ _) Hb_e x Hx.
  split=> //; apply/below_dnum => j0 Hd.
  case: (Q2 x Hx) => [Hx0 | [Ex | Ex]].
  - have [H1 _] := proj1 (Forall_forall _ _) Hbs x Hx0.
    by move/below_dnum: H1 => /(_ j0 Hd); lia.
  - by move: Hd; rewrite Ex En /= => -[<-]; lia.
  by move: Hd; rewrite Ex En /= => -[<-]; lia.
have Hfs : fscope (xf :: L) (S c) wP pp (tbr cv m (S k) (cA (pa xf)))
             sc_e wr_e.
  split=> //; split=> //; split.
    move=> p [<- | Hp] Ht.
      have Ecp : cp = true.
        by move: Ht; rewrite /cp /tbr /= Hneeds /= => ->.
      by rewrite /stored /= -En; apply: Q1.
    apply/I1/(Hrs p Hp)/(tbr_let_cont cv m k aA eA cA p (Hpk p Hp)).
    exact: Ht.
  by move=> o Ho; apply/I2/Hos.
have Htp_e : tape_fwd wP pp m (records_in cv (S k) (cA (pa xf))) sc_e wr_e.
  move=> o Ho; have [T1 T2] := Htp o Ho; split.
    move=> Hl; have [N1 N2] := T1 Hl; split=> // HT.
    case: (Q2 _ HT) => [// | [E | E]]; first by rewrite En in E.
    by have := Hown_c o Ho; move: E; rewrite En /stored => -[->]; lia.
  move=> Hl; have [N1 N2] := T2 Hl; split=> // H; apply/I2/N2.
  move: H; case: (sweep_eqb m Forward) => //=.
  by case: (trecorded _) => //= ->; rewrite orb_true_r.
have Hvo_e : vo_scope m vo sc_e wr_e.
  move=> Hm; have [V1 V2] := Hvo Hm; split.
    move=> t Evo /Q2 [H | [E | E]]; first exact: (V1 t Evo H).
      by rewrite En in E.
    by rewrite En in E.
  by move=> y Hy; apply/I2/V2.
have HF := HFb Es sc_e wr_e Hfs Htp_e Hvo_e.
apply: (good_k_weaken _ _ _ _ _ _ _ HF); first lia.
move=> sc1 wr1 J1 J2 Hb1 Hw1 [Hpost [HRV Hrev]]; split.
  move=> x /Hpost [/Q2 [H | [Ex | Ex]] | [[j0 [Hj [HF0 [Hd Hbv]]]] | Ho]].
  - by left.
  - right; left; exists c; rewrite Ex En.
    by split; [lia | split; [split=> //; left | ]].
  - right; left; exists c; rewrite Ex En.
    by split; [lia | split; [split=> //; left | ]].
  - right; left; exists j0.
    by split; [lia | split; [split=> //; right; split; [lia |] | ]].
  case: Ho => [-> | [j0 [Hjc Ex]]]; first by right; right; left.
  case: (Nat.eq_dec j0 c) => [Ej0 | Nj0].
    right; left; exists c; rewrite Ex Ej0.
    by split; [lia | split; [split=> //; left | ]].
  by right; right; right; exists j0; split=> //; lia.
split; first exact: HRV.
move=> sc2 wr2 [R1 [R2 [R3 [R4 R5]]]] Hbol Htr Hse.
have HnF : forall j0, Flet j0 -> (j0 < c1)%nat.
  by move=> j0 [_ [-> | [H _]]]; lia.
have Hcc1 : (c <= c1)%nat by lia.
have Hb21 := rscope_below Flet c c1 c3 sc2 Hcc1 HnF R4 R5.
have Hnr2 : forall x, In x sc2 -> ~ rev_new Fb (S c) c1 x.
  move=> x Hx [j0 [Hj [Hd Hor]]]; apply: (R5 x Hx); exists j0.
  split; first lia; split=> //.
  case: Hor => [-> | HnF']; first by left.
  by right=> -[_ [E | [_ HF']]] //; lia.
have Hrr : forall sc3 wr3, incl sc2 sc3 -> incl wr2 wr3 -> incl wr3 sc3 ->
    Forall (fun x => below c1 x /\ consistent x) sc3 ->
    (forall x, In x sc3 -> ~ rev_new Fb (S c) c1 x) ->
    (ac = true -> In (BarOf n) wr3) ->
    good_k sc3 wr3 c3 (rb ++ re) (fun _ _ => True).
  move=> sc3 wr3 K1 K2 K3 K4 K5 K6.
  have Hrs3 : rscope Fb (S c) c1 sc1 wr1 sc3 wr3.
    split; first by move=> y H; apply/K1/R1.
    split; first by move=> y H; apply/K2/R2.
    by split.
  have Hbo3 : bars_ok (xf :: L) (useful cv m (S k) (cA (pa xf))) wP pp wr3.
    have [B1 B2] := bars_ok_mono _ _ _ _ _ _ Hbol K2.
    split=> //; move=> p [<- | Hp] Hu Ht.
      rewrite /stored /= -En; apply: K6.
      by move: Hu Ht; rewrite /ac /useful Hneeds /= => -> ->.
    apply: B1 => //; exact: (useful_let_cont cv m k aA eA cA p (Hpk p Hp) Hu).
  have Htr3 : tape_rev wP pp (records_in cv (S k) (cA (pa xf))) wr3.
    move=> o Ho Hl Hr; apply/K2/(Htr o Ho Hl).
    by rewrite Hr orb_true_r.
  have Hse3 : expr_ok sc3 se := expr_ok_incl _ _ _ K1 Hse.
  have Hg := Hrev sc3 wr3 Hrs3 Hbo3 Htr3 Hse3.
  apply: (good_k_app _ _ c1 c3 _ _ _ _ Hg).
  move=> sc4 wr4 L1 L2 Hb4 Hw4 _.
  have Hb4' : Forall (fun x => below c2 x /\ consistent x) sc4.
    apply: (Forall_impl _ _ Hb4) => x [H1 H2]; split=> //.
    exact: below_mono H1 Hc12.
  case Eac: ac Hre K6 => Hre K6; last first.
    by move: Hre => /= [<- Ec]; subst c3; apply: good_k_nil.
  have Hsl : fold_slive cv k eA = true -> In n wr4 /\ In (TapeOf n) wr4.
    move=> Hsl.
    have Ept := fold_top L k wP pp tail eP eA eW te HeA HeW Hte Es Hsl.
    have Hm : m = Forward.
      by destruct m => //; case: (Hmr erefl Ept).
    have [A1 A2] : In n wr_e /\ In (TapeOf n) wr_e.
      by apply: Q4 => //; rewrite Hm /= Hsl.
    by split; apply/L2/K2/R2/J2.
  have Hst' : match storage wP tail eP return Prop with
              | Some m0 => n = m0 | None => True end by rewrite Es.
  have Hrt : records cv k eA = true -> storage wP tail eP <> None ->
      In (TapeOf n) wr4 by rewrite Es.
  have Hj2 : exists j0, n = DBound (j0, j0) /\ (j0 < c2)%nat.
    by exists c; split=> //; lia.
  have I14 : incl sc sc4 by move=> y H; apply/L1/K1/R1/J1/I1.
  have Hbn4 : In (BarOf n) wr4 by apply/L2/K6.
  have IH0 := IHr L k c2 wP pp vo tail eA eW eT te n ty sc4 wr4
    HeA HeW HeT (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hcc2) Hbar Hb4'
    Hw4 (Hreads sc4 I14 Eac)
    (Hbars wr4 (bars_ok_mono _ _ _ _ _ _ Hbol (fun y H => L2 y (K2 y H)))
       Eac)
    Hte Htail_ty Hj2 Hst' Hbn4 Hrt Hsl.
  cbv zeta in IH0; rewrite -/vt Hre in IH0.
  exact: (proj2 IH0).
have Hbn : ~ In (BarOf n) sc2.
  move=> I; apply: (R5 _ I); exists c; rewrite En.
  by split; [lia | split=> //; left].
case Eac: ac Hrr => Hrr; last first.
  exact: (Hrr sc2 wr2 (incl_refl _) (incl_refl _) R3 Hb21 Hnr2).
have Hte_r : te = Real.
  move/andP: Eac => [Hv _].
  have := varied_real_or_array _ _ _ _ _ _ _ _ _ HeA HeW HL Hte Hv.
  by case: (te) Hna.
rewrite Hte_r /= => rs Hrest.
apply: GoodMutable => //; first by rewrite En.
refine (Hrr (BarOf n :: sc2) (BarOf n :: wr2) _ _ _ _ _ _ rs _).
- by move=> y H; right.
- by move=> y H; right.
- by move=> y [<- | H]; [left | right; apply: R3].
- constructor=> //; split; last by rewrite En.
  by apply/below_dnum => j0; rewrite En /= => -[<-]; lia.
- move=> x [<- | Hx]; last exact: Hnr2.
  by move=> [j0 [Hj [Hd _]]]; move: Hd; rewrite En /= => -[E]; lia.
- by move=> _; left.
move=> sc' wr' L1 L2 Hb' Hw' _; apply: Hrest => //.
  by move=> y H; apply: L1; right.
by move=> y H; apply: L2; right.
Qed.

(* ---------------------------------------------------------------------------
   A replayed body: its forward sweep, then its reverse sweep, in one go. *)

(* No variable the forward sweep of a body leaves is defined again by its
   reverse sweep. *)
Lemma fwd_post_new F c c' sc sc1 :
  Forall (fun x => below c x /\ consistent x) sc ->
  fwd_post F c c' sc sc1 -> forall x, In x sc1 -> ~ rev_new F c c' x.
Proof.
move=> Hb Hp x Hx [j [Hj [Hd Hor]]].
case: (Hp x Hx) => [Hs | [[j' [Hj' [HF [Hd' Hbv]]]] | [E | [j' [Hj' E]]]]].
- have [H1 _] := proj1 (Forall_forall _ _) Hb x Hs.
  by move/below_dnum: H1 => /(_ j Hd); lia.
- rewrite Hd in Hd'; case: Hd' => E; subst j'.
  by case: Hor => [| []]; [rewrite Hbv |].
- by rewrite E in Hd.
by rewrite E /= in Hd; case: Hd => E'; lia.
Qed.

(* A replayed body, forward then reverse, with mid between them: mid may
   declare variables opened before the body, and gives the seed. *)
Lemma replay_good_mid (bP : anf pv bare) L k c wP pp vo bA bW bT ty
  (se : dexpr W) mid sc wr :
  agood_body cv bP ->
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty -> real_or_array ty ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  pp <> PTop ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  (forall p, In p L -> tbr cv Replay k bA p -> In (stored p) sc) ->
  tape_fwd wP pp Replay (records_in cv k bA) sc wr ->
  bars_ok L (useful cv Replay k bA) wP pp wr ->
  tape_rev wP pp (records_in cv k bA) wr ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo Replay
                  (rebuild _ bT (annotate_body_t cv Replay k bA)) se) c in
  (c <= c')%nat /\
  ((forall sc1 wr1, incl sc sc1 -> incl wr wr1 -> incl wr1 sc1 ->
     Forall (fun x => below c' x /\ consistent x) sc1 ->
     (forall x, In x sc1 -> In x sc \/ is_barv x = false) ->
     good_k sc1 wr1 c' mid (fun sc2 _ =>
       (forall x, In x sc2 -> In x sc1 \/ below c x) /\ expr_ok sc2 se)) ->
   good_k sc wr c' (fw ++ mid ++ rv) (fun _ _ => True)).
Proof.
move=> IH HA HW HT Hs Hroa Hbar Htc Hpp Hb Hw Hr Htp Hbo Htr.
have Hcv : Replay = Forward -> vo <> None -> cv = true by [].
have Hmf : Replay = Forward -> pp = PTop by [].
have Hmr : Replay = Replay -> pp <> PTop by move=> _.
have := IH L k c wP pp Replay vo bA bW bT ty se HA HW HT Hs Hroa Hbar Hcv
  Htc Hmf Hmr.
case: (open_pairs _ c) => [[fw rv] c'] [Hc [F HF]]; split=> // Hmid.
have Hsc : fscope L c wP pp (tbr cv Replay k bA) sc wr.
  split=> //; split=> //; split=> // o Ho.
  exact: (proj1 (proj2 Hbo o Ho)).
have Hvo : vo_scope Replay vo sc wr by [].
apply: (good_k_app _ _ c' c' _ _ _ _ (HF sc wr Hsc Htp Hvo)).
move=> sc1 wr1 I1 I2 Hb1 Hw1 [Hpost [_ Hrev]].
have Hbv : forall x, In x sc1 -> In x sc \/ is_barv x = false.
  move=> x /Hpost [H | [[j0 [_ [_ [_ H]]]] | [-> | [j0 [_ ->]]]]];
    by [left | right].
apply: (good_k_app _ _ c' c' _ _ _ _ (Hmid sc1 wr1 I1 I2 Hw1 Hb1 Hbv)).
move=> sc2 wr2 J1 J2 Hb2 Hw2 [Hn2 Hse].
have Hrs : rscope F c c' sc1 wr1 sc2 wr2.
  split=> //; split=> //; split=> //; split=> //.
  move=> x /Hn2 [H | H]; first exact: fwd_post_new Hb Hpost x H.
  move=> [j0 [Hj [Hd _]]]; move/below_dnum: H => /(_ j0 Hd); lia.
apply: Hrev => //.
- apply: (bars_ok_mono _ _ _ _ _ _ Hbo) => y Hy.
  by apply/J2/I2.
by move=> o Ho Hl Hr0; apply/J2/I2/Htr.
Qed.

Lemma replay_good (bP : anf pv bare) L k c wP pp vo bA bW bT ty
  (se : dexpr W) sc wr :
  agood_body cv bP ->
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty -> real_or_array ty ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  pp <> PTop ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  (forall p, In p L -> tbr cv Replay k bA p -> In (stored p) sc) ->
  tape_fwd wP pp Replay (records_in cv k bA) sc wr ->
  bars_ok L (useful cv Replay k bA) wP pp wr ->
  tape_rev wP pp (records_in cv k bA) wr ->
  expr_ok sc se ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo Replay
                  (rebuild _ bT (annotate_body_t cv Replay k bA)) se) c in
  (c <= c')%nat /\ good_k sc wr c' (fw ++ rv) (fun _ _ => True).
Proof.
move=> IH HA HW HT Hs Hroa Hbar Htc Hpp Hb Hw Hr Htp Hbo Htr Hse.
have := replay_good_mid bP L k c wP pp vo bA bW bT ty se [] sc wr IH HA HW
  HT Hs Hroa Hbar Htc Hpp Hb Hw Hr Htp Hbo Htr.
case: (open_pairs _ c) => [[fw rv] c'] [Hc Hg]; split=> //.
apply: Hg => sc1 wr1 I1 _ Hw1 Hb1 _; apply: good_k_nil => //.
by split; [left | exact: expr_ok_incl I1 Hse].
Qed.

(* The reads and the flows of a replayed body, for a variable in scope. *)
Lemma tbr_ite_then k (cA : atom avar) tA eA (p : pv) :
  tbr cv Replay k tA p -> vreads cv k (AIte cA tA eA) p.
Proof.
rewrite /tbr /vreads /=.
case: (needs cv Replay k tA) => ut lt; case: (needs cv Replay k eA) => ue le.
by rewrite /= !atom_member_union => ->; rewrite orb_true_r.
Qed.

Lemma tbr_ite_else k (cA : atom avar) tA eA (p : pv) :
  tbr cv Replay k eA p -> vreads cv k (AIte cA tA eA) p.
Proof.
rewrite /tbr /vreads /=.
case: (needs cv Replay k tA) => ut lt; case: (needs cv Replay k eA) => ue le.
by rewrite /= !atom_member_union => ->; rewrite !orb_true_r.
Qed.

Lemma useful_ite_then k (cA : atom avar) tA eA (p : pv) :
  useful cv Replay k tA p -> vflows cv k (AIte cA tA eA) p.
Proof.
rewrite /useful /vflows /=.
case: (needs cv Replay k tA) => ut lt; case: (needs cv Replay k eA) => ue le.
by rewrite /= !atom_member_union => ->.
Qed.

Lemma useful_ite_else k (cA : atom avar) tA eA (p : pv) :
  useful cv Replay k eA p -> vflows cv k (AIte cA tA eA) p.
Proof.
rewrite /useful /vflows /=.
case: (needs cv Replay k tA) => ut lt; case: (needs cv Replay k eA) => ue le.
by rewrite /= !atom_member_union => ->; rewrite orb_true_r.
Qed.

Lemma tbr_map_body k (loA hiA : atom avar) bA (p : pv) :
  (aid (pa p) < k)%nat ->
  tbr cv Replay (S k) (bA (fresh k)) p -> vreads cv k (AMap loA hiA bA) p.
Proof.
move=> Hp; rewrite /tbr /vreads /=.
case: (needs cv Replay (S k) (bA (fresh k))) => u l /= H.
by rewrite atom_member_union atom_member_remove ?H ?orb_true_r //;
  apply: same_term_below.
Qed.

Lemma useful_map_body k (loA hiA : atom avar) bA (p : pv) :
  (aid (pa p) < k)%nat ->
  useful cv Replay (S k) (bA (fresh k)) p -> vflows cv k (AMap loA hiA bA) p.
Proof.
move=> Hp; rewrite /useful /vflows /=.
case: (needs cv Replay (S k) (bA (fresh k))) => u l /= H.
by rewrite atom_member_remove ?H //; apply: same_term_below.
Qed.

(* A branch: both bodies are replayed, forward then reverse, in a branch on
   the same condition. *)
Lemma agood_rev_ite (cP : atom pv) (tP eP : anf pv bare) :
  agood_body cv tP -> agood_body cv eP -> agood_rev cv (AIte cP tP eP).
Proof.
move=> IHt IHe.
arev_intro.
rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT.
rename H6 into HAt, H7 into HAe, H3 into HWt, H4 into HWe, H0 into HTt,
  H1 into HTe, H into HcL.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc *.
have Hnot : forall ix sx, pp <> PArray ix sx.
  by move=> ix sx E; rewrite E /= in Htc.
case Ecb: (ty_eqb (of_atom (amap pw cP)) Boolean) Htc => Htc;
  last by destruct pp as [| | | ix sx]; rewrite /= in Htc.
have Htc' : (let '(t3, d1) :=
               typecheck (option_map (amap pw) wP) InBranch k tW in
             let '(t4, d2) :=
               typecheck (option_map (amap pw) wP) InBranch k eW in
             if is_ok d1 then if is_ok d2 then
               if ty_eqb t3 Real && ty_eqb t4 Real then (Real, Ok)
               else (Real, Error "both branches must compute a real")
             else (Real, d2) else (Real, d1)) = (te, Ok).
  by destruct pp as [| | | ix sx]; [| | | case: (Hnot ix sx)].
clear Htc.
case HtW: (typecheck (option_map (amap pw) wP) InBranch k tW) Htc'
  => [t3 d1] Htc'.
case HeW: (typecheck (option_map (amap pw) wP) InBranch k eW) Htc'
  => [t4 d2] Htc'.
destruct d1, d2; rewrite /= in Htc'; try discriminate.
move: Htc'; case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= _.
move/ty_eqb_true: E3 => E3; move/ty_eqb_true: E4 => E4; subst t3 t4.
set n := DBound (j, j) in Hbn *.
set eV := AIte (amap pa cP) tA eA.
(* a branch body, replayed *)
have Hbr : forall bP bA bW bT (cb cb' : nat) fw rv,
    anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
    agood_body cv bP -> (c <= cb)%nat ->
    (forall p, live_anf k bW p ->
       live_value k (AIte (amap pw cP) tW eW) p) ->
    typecheck (option_map (amap pw) wP) InBranch k bW = (Real, Ok) ->
    (forall p, tbr cv Replay k bA p -> vreads cv k eV p) ->
    (forall p, useful cv Replay k bA p -> vflows cv k eV p) ->
    open_pairs (adj W (option_map (amap pt) wP) vo Replay
                  (rebuild (tvar W) bT (annotate_body_t cv Replay k bA))
                  (DVar (BarOf n))) cb = ((fw, rv), cb') ->
    (cb <= cb')%nat /\ good_k sc wr cb' (fw ++ rv) (fun _ _ => True).
  move=> bP bA bW bT cb cb' fw rv HA' HW' HT' IH Hcb Hl Htb Hrb Hub Hob.
  have Hs' : sctx L k cb wP PBranch (live_anf k bW) Real.
    apply: (sctx_sub L k cb wP pp PBranch
              (live_value k (AIte (amap pw cP) tW eW)) _ ty) => //.
    by apply: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs); auto.
  have Hbcb : Forall (fun x => below cb x /\ consistent x) sc.
    apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
    exact: (below_mono _ _ _ Y1 Hcb).
  have Hpb : PBranch <> PTop by [].
  have Htf : tape_fwd wP PBranch Replay (records_in cv k bA) sc wr.
    by move=> o E.
  have Hbo' : bars_ok L (useful cv Replay k bA) wP PBranch wr.
    split; last by move=> o E.
    by move=> p Hp Hu Ht; apply: (proj1 Hbo) => //; apply: Hub.
  have Htr : tape_rev wP PBranch (records_in cv k bA) wr by move=> o E.
  have Hse : expr_ok sc (DVar (BarOf n)) by apply: Hw.
  have := replay_good bP L k cb wP PBranch vo bA bW bT Real (DVar (BarOf n))
    sc wr IH HA' HW' HT' Hs' I Hbar Htb Hpb Hbcb Hw
    (fun p Hp Ht => Hrd p Hp (Hrb p Ht)) Htf Hbo' Htr Hse.
  by rewrite Hob.
rewrite open_pairs_sbind.
case Hot: (open_pairs (adj W (option_map (amap pt) wP) vo Replay
  (rebuild (tvar W) tT (annotate_body_t cv Replay k tA))
  (DVar (BarOf n))) c) => [[ft rt] c1].
rewrite open_pairs_sbind.
case Hoe: (open_pairs (adj W (option_map (amap pt) wP) vo Replay
  (rebuild (tvar W) eT (annotate_body_t cv Replay k eA))
  (DVar (BarOf n))) c1) => [[fe re] c2].
cbn [open_pairs].
have Hlt : forall p, live_anf k tW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' orb_true_r.
have Hle : forall p, live_anf k eW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' !orb_true_r.
have [Hc1 Hg1] := Hbr tP tA tW tT c c1 ft rt HAt HWt HTt IHt (le_n c) Hlt
  HtW (tbr_ite_then k _ tA eA) (useful_ite_then k _ tA eA) Hot.
have [Hc2 Hg2] := Hbr eP eA eW eT c1 c2 fe re HAe HWe HTe IHe Hc1 Hle HeW
  (tbr_ite_else k _ tA eA) (useful_ite_else k _ tA eA) Hoe.
split; first lia.
move=> rest Hrest /=.
have Hc : expr_ok sc (spell (amap pt cP)).
  apply: (spell_scope L k) => // r Er; split; first exact: HcL.
  apply: Hrd (HcL r Er) _; rewrite /vreads /= Er /=.
  case: (needs cv Replay k tA) => ? ?; case: (needs cv Replay k eA) => ? ?.
  by rewrite /= !atom_member_union /= Nat.eqb_refl.
apply: GoodBranch; [exact: Hc | exact: good_k_good Hg1 |
                    exact: good_k_good Hg2 |].
apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw | by []].
apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
by apply: (below_mono c _ _ Y1); lia.
Qed.

(* A map: its body is replayed in a reverse loop, with the adjoint of the
   element as seed. *)
Lemma agood_rev_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, agood_body cv (bP x)) -> agood_rev cv (AMap loP hiP bP).
Proof.
move=> IHb.
arev_intro.
rename b into bA, b0 into bW, b1 into bT, H7 into HbA, H4 into HbW,
  H1 into HbT.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc *.
destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
destruct tail; last discriminate.
destruct loP as [? | ? | l0]; rewrite /= in Htc; try discriminate.
destruct hiP as [? | ? | h]; rewrite /= in Htc; try discriminate.
move: Htc; case El: (~~ (l0 =? 0)%Z) => // Htc.
move/negbFE/Z.eqb_eq: El => El; subst l0.
have Hte : te = Array (h - 0) by clear - Htc; crush_match Htc.
have Hra : is_array ty by rewrite -(Htail erefl) Hte.
case Eo: (owner wP PTop) => [o |]; last first.
  by case: (s_ty _ _ _ _ _ _ _ Hs Hra Eo).
destruct wP as [[o' | |] |]; rewrite /= in Eo; try discriminate.
case Ey: (vty (pw o')) Eo => [| | | ny] // [Eo]; subst o'.
rewrite /= in Hst.
have HtB : typecheck (Some (AVar (pw o))) ScalarBody (S k)
             (bW (VInfo k Integer None)) = (Real, Ok).
  move: Htc => /=; case: (varg (pw o)) => [[nm [] ] |] /=;
    case: (occurs_anf (vid (pw o)) (S k) (bW (anon k))) => //;
    case: (typecheck (Some (AVar (pw o))) ScalarBody (S k)
             (bW (VInfo k Integer None))) => [tb [| mm]] //=;
    by case Etb: (ty_eqb tb Real) => // _; move/ty_eqb_true: Etb => ->.
have [o'' [[Eo''] [HoL _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
subst o''.
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[fw rv] c2].
cbn [open_pairs].
set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
            (VInt 0) c.
have Hs' : sctx (ix :: L) (S k) (S c) (Some (AVar o)) PScalar
             (live_anf (S k) (bW (VInfo k Integer None))) Real.
  apply: sctx_scalar.
  - constructor.
      by repeat split; rewrite /=; auto; try lia; discriminate.
    apply: (Forall_impl _ _ HL) => p Hp.
    by apply: (static_mono k _ p Hp); lia.
  - move=> p q [Ep | Hp] [Eq | Hq] E; subst => //;
      try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; rewrite /= in E; lia);
      try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; rewrite /= in E; lia).
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
  - move=> p [<- /= | Hp]; first lia.
    by move: (s_num _ _ _ _ _ _ _ Hs _ Hp) => /=; lia.
  move=> a0 [<-]; exists o; split=> //; split; first by right.
  by have [? [[Ex] [_ Hg]]] := s_written _ _ _ _ _ _ _ Hs _ erefl; subst.
have Hcons : Forall (fun x => below (S c) x /\ consistent x)
               (DBound (c, c) :: sc).
  constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
have Hpk : forall p, In p L -> (aid (pa p) < k)%nat by exact: aids_below.
have Hbarx : forall p, In p (ix :: L) -> tbar (pt p) = avaried (pa p).
  by move=> p [<- | Hp] //; apply: Hbar.
have Hrx : forall p, In p (ix :: L) ->
    tbr cv Replay (S k) (bA (fresh k)) p ->
    In (stored p) (DBound (c, c) :: sc).
  move=> p [<- | Hp] Ht; first by left.
  by right; apply: (Hrd p Hp); apply: tbr_map_body (Hpk p Hp) Ht.
have Htf : tape_fwd (Some (AVar o)) PScalar Replay
    (records_in cv (S k) (bA (fresh k))) (DBound (c, c) :: sc) wr.
  by move=> o' E.
have Hbo' : bars_ok (ix :: L) (useful cv Replay (S k) (bA (fresh k)))
    (Some (AVar o)) PScalar wr.
  split; last by move=> o' E.
  move=> p [<- | Hp] Hu Ht //.
  by apply: (proj1 Hbo) => //; apply: useful_map_body (Hpk p Hp) Hu.
have Htr : tape_rev (Some (AVar o)) PScalar
    (records_in cv (S k) (bA (fresh k))) wr by move=> o' E.
have Hse : expr_ok (DBound (c, c) :: sc)
    (DAt (DVar (BarOf (DBound (j, j)))) (DVar (DBound (c, c)))).
  by split; [right; apply: Hw | left].
have Hws : incl wr (DBound (c, c) :: sc) by move=> y Hy; right; apply: Hw.
have Hpp : PScalar <> PTop by [].
have := replay_good (bP ix) (ix :: L) (S k) (S c) (Some (AVar o)) PScalar vo
  (bA (fresh k)) (bW (VInfo k Integer None))
  (bT (open_index (DBound (c, c)))) Real _ (DBound (c, c) :: sc) wr
  (IHb ix) (HbA ix _) (HbW ix _) (HbT ix _) Hs' I Hbarx HtB Hpp Hcons Hws
  Hrx Htf Hbo' Htr Hse.
rewrite Hob => -[Hc2 Hg].
split; first lia.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
move=> rest Hrest /=.
apply: GoodForBack; [exact: Hni | by [] | exact I | exact I | |].
  exact: good_k_good Hg.
apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw | by []].
apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
by apply: (below_mono c _ _ Y1); lia.
Qed.

(* The index the reverse loop of an in-place fold pops into: the loop index
   or a literal, as the typing of the body of an in-place fold requires. *)
Lemma tail_index_ok (bP : anf pv bare) : forall L k wP ix sx bW bT
  (t : ltree) te,
  (forall p, In p L -> (vid (pw p) < k)%nat) -> ids_unique L -> In ix L ->
  anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (pw ix)) (AVar (pw sx))) k bW = (te, Ok) ->
  exists iP, (iP = AVar ix \/ exists z, iP = ANat z) /\
    tail_index W (rebuild _ bT t) = spell (amap pt iP).
Proof.
elim: bP => [a e cP IH | x] /= L k wP ix sx bW bT t te Hk Hu Hix HW HT Htc;
  last first.
  by case: bT HT => // ? _; exists (ANat 0); split; [right; exists 0%Z |].
case: bW HW Htc => [aW eW cW | ?] //= [HeW HcW] Htc.
case: bT HT => [aT eT cT | ?] //= [HeT HcT].
case Etv: (typecheck_value _ _ _ _ eW) Htc => [te0 d0].
case: d0 Etv => //= Etv Htc.
set x := PV (AV k false) (VInfo k te0 None) (probe W) (VInt 0) k.
have HxL : ~ In x L by move=> Hx; have := Hk x Hx; rewrite /=; lia.
have Hk' : forall p, In p (x :: L) -> (vid (pw p) < S k)%nat.
  by move=> p [<- | Hp] /=; [lia | have := Hk p Hp; lia].
have Hu' : ids_unique (x :: L).
  move=> p p' [<- | Hp] [<- | Hp'] E //;
    [have := Hk p' Hp' | have := Hk p Hp | exact: Hu]; rewrite /= in E; lia.
(* the index of the rest of the body *)
have Hrest : forall rest, exists iP,
    (iP = AVar ix \/ exists z, iP = ANat z) /\
    tail_index W (rebuild _ (cT (probe W)) rest) = spell (amap pt iP).
  by move=> rest; apply: (IH x (x :: L) (S k) wP ix sx _ _ rest te Hk' Hu'
    (or_intror Hix) (HcW x _) (HcT x _) Htc).
case: t => [a0 vt rest |] /=;
  case: eT HeT => [f0 a1 | f0 a1 b1 | a1 i1 | a1 i1 v1 | c1 t1 e1 | lo hi b1
                  | an lo hi i0 b1] HeT /=; try by apply: Hrest.
all: try (by case: vt; intros; simpl; apply: Hrest).
(* the final set *)
all: case: (is_tail _); last by apply: Hrest.
all: case: e HeW HeT => // aP iP vP HeW HeT.
all: case: eW HeW Etv => // aW' iW vW [_ [HiW _]] Etv.
all: case: HeT => _ [HiT _].
all: have [EiW HiL] := atom_graph pw L iP iW HiW.
all: have [EiT _] := atom_graph pt L iP i1 HiT; subst iW i1.
all: move: Etv => /=; case: (of_atom aW') => // n0.
all: case: ifP => // /andP [_ Eidx] _.
all: exists iP; split=> //.
all: move: Eidx; case: iP HiL HiT HiW => [p | s | z] HiL _ _ /=;
  [rewrite orbF => /Nat.eqb_eq E; left; congr AVar;
   exact: (Hu p ix (HiL p erefl) Hix E) | by [] | by right; exists z].
Qed.

Lemma tbr_fold_body k an (loA hiA initA : atom avar) bA (p : pv) :
  (aid (pa p) < k)%nat ->
  tbr cv Replay (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) p ->
  vreads cv k (AFold an loA hiA initA bA) p.
Proof.
move=> Hp; rewrite /tbr /vreads /= /fold_binders.
case: (needs _ _ _ _) => u l /= H.
have H1 : (aid (pa p) < S k)%nat by lia.
rewrite atom_member_union !atom_member_remove ?H ?orb_true_r //.
  by apply: same_term_below.
by apply: same_term_below.
Qed.

Lemma useful_fold_body k an (loA hiA initA : atom avar) bA (p : pv) :
  (aid (pa p) < k)%nat ->
  useful cv Replay (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) p ->
  vflows cv k (AFold an loA hiA initA bA) p.
Proof.
move=> Hp; rewrite /useful /vflows /= /fold_binders.
case: (needs _ _ _ _) => u l /= H.
have H1 : (aid (pa p) < S k)%nat by lia.
rewrite atom_member_union !atom_member_remove ?H ?orb_true_r //.
  by apply: same_term_below.
by apply: same_term_below.
Qed.

Lemma reads_fold_bounds k an (loA hiA initA : atom avar) bA (q : avar) :
  loA = AVar q \/ hiA = AVar q ->
  atom_member (AVar q)
    (fst (value_needs cv k (AFold an loA hiA initA bA))) = true.
Proof.
move=> H; rewrite [value_needs _ _ _]/= /fold_binders.
case: (needs _ _ _ _) => u l.
rewrite [fst _]/= !atom_member_union.
by case: H => ->; rewrite atom_member_var ?orb_true_r.
Qed.

Lemma agood_rev_fold a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (forall x y, agood_body cv (bP x y)) ->
  agood_rev cv (AFold a loP hiP initP bP).
Proof.
move=> IHb.
arev_intro.
rename b into bA, b0 into bW, b1 into bT, H10 into HbA, H6 into HbW,
  H2 into HbT, H into HloL, H0 into HhiL, H1 into HiL.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hpk : forall p, In p L -> (aid (pa p) < k)%nat by exact: aids_below.
move: Htc => /=; case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
                     ty_eqb (of_atom (amap pw hiP)) Integer) => // Htc.
have Hlo : expr_ok sc (spell (amap pt loP)).
  apply: (spell_scope L k) => // r Er; split; first exact: HloL.
  apply: (Hrd r (HloL r Er)); rewrite /vreads.
  by apply: reads_fold_bounds; left; rewrite Er.
have Hhi : expr_ok sc (spell (amap pt hiP)).
  apply: (spell_scope L k) => // r Er; split; first exact: HhiL.
  apply: (Hrd r (HhiL r Er)); rewrite /vreads.
  by apply: reads_fold_bounds; right; rewrite Er.
set svr := fold_varied k (amap pa initP) bA.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
have Hbc : forall c', (c <= c')%nat ->
    Forall (fun x => below c' x /\ consistent x) sc.
  move=> c' Hc'; apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  exact: (below_mono c _ _ Y1 Hc').
cbn [annotate_value_t rebuild_value fold_binders fold_ann].
move: Htc; case Er: (ty_eqb (of_atom (amap pw initP)) Real) => Htc.
  (* a real state: its adjoint flows back through the reverse loop *)
  move/ty_eqb_true: Er => Er.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
  case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
              (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
    => [tb [| mm]] Htc; rewrite /= in Htc; try discriminate.
  case Etb: (ty_eqb tb Real) Htc => Htc; rewrite /= in Htc; try discriminate.
  move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => Ete; subst te.
  cbn [open_pairs]; rewrite open_pairs_sbind.
  case Hob: (open_pairs _ (S (S c))) => [[fw rv] c2].
  cbn [open_pairs].
  set n := DBound (j, j) in Hob Hsl Hbn Hrt *.
  set ix := PV (AV k false) (VInfo k Integer None)
              (TVar (DBound (c, c)) Integer None false false false false None)
              (VInt 0) c.
  set sx := PV (AV (S k) svr) (VInfo (S k) Real None)
              (TVar n Real None svr svr svr false None) (VReal (Dual 0 0)) j.
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k))
        (bW (VInfo k Integer None) (VInfo (S k) Real None)) p ->
      live_value k
        (AFold ann0 (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
    move=> p Hp Hl; rewrite /live_anf /live_value /= in Hl *.
    by rewrite -(live_cont2 L k bP bW (pfresh k) (pfresh (S k))
                  (VInfo k Integer None) (VInfo (S k) Real None)
                  _ HbW HL erefl erefl erefl erefl) Hl !orb_true_r.
  have Hs' : sctx (sx :: ix :: L) (S (S k)) (S (S c)) wP PScalar
      (live_anf (S (S k))
         (bW (VInfo k Integer None) (VInfo (S k) Real None))) Real.
    apply: sctx_scalar.
    - constructor.
        by repeat split; rewrite /=; auto; try lia; discriminate.
      constructor.
        by repeat split; rewrite /=; auto; try lia; discriminate.
      apply: (Forall_impl _ _ HL) => p Hp.
      by apply: (static_mono k _ p Hp); lia.
    - move=> p q [Ep | [Ep | Hp]] [Eq | [Eq | Hq]] E;
        try subst p; try subst q; rewrite /= in E; try reflexivity; try lia;
        try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; lia);
        try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; lia).
      exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by move: (s_num _ _ _ _ _ _ _ Hs _ Hp) => /=; lia.
    move=> a0 E; have [y [-> [Hy Hg]]] := s_written _ _ _ _ _ _ _ Hs _ E.
    by exists y; split=> //; split; first by right; right.
  have Hcons : Forall (fun x => below (S (S c)) x /\ consistent x)
                 (DBound (c, c) :: sc).
    by constructor; [split=> /=; [lia | by []] | apply: Hbc; lia].
  have Hbarx : forall p, In p (sx :: ix :: L) ->
      tbar (pt p) = avaried (pa p).
    by move=> p [<- | [<- | Hp]] //; apply: Hbar.
  have Hrx : forall p, In p (sx :: ix :: L) ->
      tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)) p ->
      In (stored p) (DBound (c, c) :: sc).
    move=> p [<- | [<- | Hp]] Ht; last 1 first.
    - by right; apply: (Hrd p Hp); apply: tbr_fold_body (Hpk p Hp) Ht.
    - by right; apply/Hw; exact: (proj1 (Hsl Ht)).
    by left.
  have Htf : tape_fwd wP PScalar Replay
      (records_in cv (S (S k)) (bA (pa ix) (pa sx)))
      (DBound (c, c) :: sc) wr.
    by move=> o E.
  have Hbo' : bars_ok (sx :: ix :: L)
      (useful cv Replay (S (S k)) (bA (pa ix) (pa sx))) wP PScalar wr.
    split; last by move=> o E.
    move=> p [<- | [<- | Hp]] Hu Ht //.
    by apply: (proj1 Hbo) => //; apply: useful_fold_body (Hpk p Hp) Hu.
  have Htr : tape_rev wP PScalar
      (records_in cv (S (S k)) (bA (pa ix) (pa sx))) wr by move=> o E.
  have Hws : incl wr (DBound (c, c) :: sc) by move=> y Hy; right; apply: Hw.
  have Hpp : PScalar <> PTop by [].
  have := replay_good_mid (bP ix sx) (sx :: ix :: L) (S (S k)) (S (S c)) wP
    PScalar vo (bA (pa ix) (pa sx))
    (bW (VInfo k Integer None) (VInfo (S k) Real None)) (bT (pt ix) (pt sx))
    Real (DVar (BarOf (DBound (S c, S c))))
    [DDefine (DConstant Real) (BarOf (DBound (S c, S c))) (DVar (BarOf n));
     DAssign (DVar (BarOf n)) (DReal "0")]
    (DBound (c, c) :: sc) wr (IHb ix sx) (HbA ix _ sx _) (HbW ix _ sx _)
    (HbT ix _ sx _) Hs' I Hbarx HtB Hpp Hcons Hws Hrx Htf Hbo' Htr.
  rewrite Hob => -[Hc2 Hg].
  split; first lia.
  (* mid: the adjoint of the state moves to a fresh variable *)
  have Hbody : good_k (DBound (c, c) :: sc) wr c2 (fw ++
      [DDefine (DConstant Real) (BarOf (DBound (S c, S c))) (DVar (BarOf n));
       DAssign (DVar (BarOf n)) (DReal "0")] ++ rv) (fun _ _ => True).
    apply: Hg => sc1 wr1 I1 I2 Hw1 Hb1 Hbv rest Hrest /=.
    have Hnb : ~ In (BarOf (DBound (S c, S c))) sc1.
      move=> /Hbv [[E | H] | //]; first by [].
      have [H1 _] := proj1 (Forall_forall _ _) Hb _ H.
      by rewrite /= in H1; lia.
    apply: GoodConstant => //; first by apply/Hw1/I2.
    apply: GoodAssign; [by apply/I2 | by [] |].
    apply: Hrest; [by move=> y Hy; right | by [] | | | ].
    - constructor=> //; split=> //=; lia.
    - by move=> y Hy; right; apply: Hw1.
    split; last by left.
    move=> x [<- | Hx]; last by left.
    by right=> /=; lia.
  move=> rest Hrest /=.
  apply: GoodForBack; [exact: Hni | by [] | exact: Hlo | exact: Hhi | |].
    have Hgb := good_k_good _ _ _ _ _ Hbody.
    case Esl: (state_live cv k (amap pa initP) bA) => //=.
    have [Hn1 Hn2] := Hsl Esl.
    by apply: GoodPop => //; apply: Hws.
  case Ebi: (bar (amap pt initP)) => [bi |] /=; last first.
    apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw | by []].
    by apply: Hbc; lia.
  have [q [Eq [Hq [Hvq Ebq]]]] := bar_atom L k initP bi HL Hbar HiL Ebi.
  subst bi.
  have Hfq : vflows cv k
      (AFold ann (amap pa loP) (amap pa hiP) (amap pa initP) bA) q.
    rewrite /vflows Eq [value_needs _ _ _]/= /fold_binders.
    case: (needs _ _ _ _) => u l.
    by rewrite [snd _]/= atom_member_union atom_member_var.
  apply: GoodIncrement.
  - by apply: (proj1 Hbo q Hq Hfq); rewrite Hbar.
  - by apply: Hw.
  apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw | by []].
  by apply: Hbc; lia.
(* an array updated in place *)
case Eat: (of_atom (amap pw initP)) Htc => [| | | z] Htc //.
destruct initP as [o | | ]; rewrite /= in Eat Htc; try discriminate.
have Ho' : In o L by apply: HiL.
have Hown : owner wP pp = Some o /\ tail = true.
  destruct pp as [| | | ix0 sx0]; destruct tail; rewrite /= in Htc;
    try discriminate.
  - destruct wP as [y |] eqn:Ew; rewrite /= in Htc; last discriminate.
    move: Htc; case E: (match amap pw y with
                        | AVar y0 => (vid (pw o) =? vid y0)%nat
                        | _ => false end) => // Htc.
    have [Ey] := unique_written_s _ _ _ _ _ _ _ _ _ Hs Ho' erefl E; subst y.
    by rewrite /= Eat.
  move: Htc; case E: (vid (pw o) =? vid (pw sx0))%nat => //= Htc.
  have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
  by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs Ho' Hsx E).
case: Hown => Hown Et; subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true
                (AVar (pw o)) = true.
  by move: Htc; case: (in_place_init _ _ _ _).
rewrite Hin_pl in Htc.
move: Htc; case Hocc: (occurs_anf (vid (pw o)) (S (S k))
                         (bW (anon k) (anon (S k)))) => Htc.
  by case: (varg (pw o)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP)
             (ArrayBody (AVar (VInfo k Integer None))
                        (AVar (VInfo (S k) (Array z) None)))
             (S (S k))
             (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)))
  Htc => [tb [| mm]] Htc; rewrite /= in Htc; try discriminate.
case Etb: (ty_eqb tb (Array z)) Htc => Htc; rewrite /= in Htc;
  try discriminate.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))))
  Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => Ete; subst te.
rewrite /= Eat in Hst; case: Hst => Ej; subst j.
move=> _.
set n := DBound (pn o, pn o) in Hbn Hsl Hrt *.
have Hlivo : live_value k (AFold Bare (amap pw loP) (amap pw hiP)
                             (AVar (pw o)) bW) o.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
have Hvo : avaried (pa o) = true.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hown; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate.
    destruct (vty (pw y)) eqn:Evy; try discriminate.
    case: Hown => Ey; subst y.
    have Hia : is_array (vty (pw o)) by rewrite Eat.
    have [_ Hv] := s_top _ _ _ _ _ _ _ Hs o erefl erefl Hia.
    exact: Hv Hlivo.
  case: Hown => Eo; subst sx0.
  by have [_ [_ [_ [_ [Hv _]]]]] := s_place _ _ _ _ _ _ _ Hs.
have Hsvr : svr = true by rewrite /svr /fold_varied /= Hvo.
cbn [open_pairs]; rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[fw rv] c2].
cbn [open_pairs].
set ix := PV (AV k false) (VInfo k Integer None)
            (TVar (DBound (c, c)) Integer None false false false false None)
            (VInt 0) c.
set sx := PV (AV (S k) svr) (VInfo (S k) (Array z) None)
            (TVar n (Array z) None svr svr svr false None)
            (default_dual (Array z)) (pn o).
have Hlive_b : forall p, In p L ->
    live_anf (S (S k))
      (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) p ->
    live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw o)) bW) p
    /\ p <> o.
  move=> p Hp Hl.
  have E2 := live_cont2 L k bP bW (pfresh k) (pfresh (S k))
               (VInfo k Integer None) (VInfo (S k) (Array z) None)
               (vid (pw p)) HbW HL erefl erefl erefl erefl.
  rewrite /live_anf E2 in Hl.
  split; first by rewrite /live_value /= Hl !orb_true_r.
  by move=> Ep; subst p; congruence.
have Hs' : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx)
    (live_anf (S (S k)) (bW (VInfo k Integer None)
                            (VInfo (S k) (Array z) None))) (Array z).
  have [D1 D2] := default_dual_ok (Array z).
  constructor.
  - constructor.
      by repeat split; rewrite /=; auto; try lia; discriminate.
    constructor.
      by repeat split; rewrite /=; auto; try lia; discriminate.
    apply: (Forall_impl _ _ HL) => p Hp.
    by apply: (static_mono k _ p Hp); lia.
  - move=> p q [Ep | [Ep | Hp]] [Eq | [Eq | Hq]] E;
      try subst p; try subst q; rewrite /= in E; try reflexivity; try lia;
      try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; lia);
      try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; lia).
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
  - move=> p [<- | [<- | Hp]] /=; try lia.
    by move: (s_num _ _ _ _ _ _ _ Hs _ Hp) => /=; lia.
  - move=> a0 E; have [y [-> [Hy Hg]]] := s_written _ _ _ _ _ _ _ Hs _ E.
    by exists y; split=> //; split; first by right; right.
  - by rewrite /=; repeat split; auto; change (svr = true); exact: Hsvr.
  - move=> o' p Ho2 Hp Ep; rewrite /= in Ho2; case: Ho2 => Eo2; subst o'.
    case: Hp => [Ep' | [Ep' | Hp]]; try subst p;
      [by left | by rewrite /= in Ep; lia |].
    right=> Hl; have [Hl' Hpo'] := Hlive_b p Hp Hl.
    by case: (s_owner _ _ _ _ _ _ _ Hs o p Hown Hp Ep).
  - move=> p o' Hp Lp Ha Hg Ho2; rewrite /= in Ho2; case: Ho2 => Eo2.
    subst o'; case: Hp => [Ep' | [Ep' | Hp]]; try subst p;
      [by [] | by case: Ha |].
    have [Hl' _] := Hlive_b p Hp Lp.
    exact: (s_arrays _ _ _ _ _ _ _ Hs p o Hp Hl' Ha Hg Hown).
  - by [].
  by [].
have [Bo1 Bo2] := proj2 Hbo o Hown.
have Hcons : Forall (fun x => below (S c) x /\ consistent x)
               (DBound (c, c) :: sc).
  by constructor; [split=> /=; [lia | by []] | apply: Hbc; lia].
have Hbarx : forall p, In p (sx :: ix :: L) ->
    tbar (pt p) = avaried (pa p).
  by move=> p [<- | [<- | Hp]] //; apply: Hbar.
have Hrx : forall p, In p (sx :: ix :: L) ->
    tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)) p ->
    In (stored p) (DBound (c, c) :: sc).
  move=> p [<- | [<- | Hp]] Ht; last 1 first.
  - by right; apply: (Hrd p Hp); apply: tbr_fold_body (Hpk p Hp) Ht.
  - by right; apply/Hw.
  by left.
(* the state is the storage the body updates in place *)
have Htf : tape_fwd wP (PArray ix sx) Replay
    (records_in cv (S (S k)) (bA (pa ix) (pa sx))) (DBound (c, c) :: sc) wr.
  by move=> o' Ho2; rewrite /= in Ho2; case: Ho2 => <-.
have Hbo' : bars_ok (sx :: ix :: L)
    (useful cv Replay (S (S k)) (bA (pa ix) (pa sx))) wP (PArray ix sx) wr.
  split; last by move=> o' Ho2; rewrite /= in Ho2; case: Ho2 => <-.
  move=> p [<- | [<- | Hp]] Hu Ht //.
  by apply: (proj1 Hbo) => //; apply: useful_fold_body (Hpk p Hp) Hu.
have Htr : tape_rev wP (PArray ix sx)
    (records_in cv (S (S k)) (bA (pa ix) (pa sx))) wr.
  move=> o' Ho2 _ Hr0; rewrite /= in Ho2; case: Ho2 => <-.
  apply: Hrt; last by rewrite /= Eat.
  by rewrite /= /fold_binders -/svr Hr0 orb_true_r.
have Hws : incl wr (DBound (c, c) :: sc) by move=> y Hy; right; apply: Hw.
have Hpp : PArray ix sx <> PTop by [].
have Hse : expr_ok (DBound (c, c) :: sc) (DReal "0") by [].
have := replay_good (bP ix sx) (sx :: ix :: L) (S (S k)) (S c) wP
  (PArray ix sx) vo (bA (pa ix) (pa sx))
  (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
  (bT (pt ix) (pt sx)) (Array z) (DReal "0") (DBound (c, c) :: sc) wr
  (IHb ix sx) (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) Hs' I Hbarx
  HtB Hpp Hcons Hws Hrx Htf Hbo' Htr Hse.
rewrite Hob => -[Hc2 Hg].
split; first lia.
move=> rest Hrest /=.
apply: GoodForBack; [exact: Hni | by [] | exact: Hlo | exact: Hhi | |].
  (* the pop restores the element the step overwrote *)
  have Hgb := good_k_good _ _ _ _ _ Hg.
  case Esl: (state_live cv k (amap pa (AVar o)) bA) => //=.
  have [Hn1 Hn2] := Hsl Esl.
  apply: GoodPop => //.
  split=> //.
  have HsL := s_static _ _ _ _ _ _ _ Hs'.
  have Hk' : forall p, In p (sx :: ix :: L) -> (vid (pw p) < S (S k))%nat.
    by move=> p Hp; have [_ [H _]] := static_in _ _ _ HsL Hp.
  have [iP [Hi Eti]] := tail_index_ok (bP ix sx) (sx :: ix :: L) (S (S k))
    wP ix sx _ (bT (pt ix) (pt sx)) (annotate_body_t cv Replay (S (S k))
      (bA (pa ix) (pa sx))) (Array z) Hk' (s_unique _ _ _ _ _ _ _ Hs')
    (or_intror (or_introl erefl)) (HbW ix _ sx _) (HbT ix _ sx _) HtB.
  rewrite Eti.
  by case: Hi => [-> | [z' ->]] /=; [left |].
apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw | by []].
by apply: Hbc; lia.
Qed.

(* The adjoint code keeps the discipline, for every body (adj) and every
   value (rev_value), from the forward part for the values (fwd_value). *)
Theorem agood_adj :
  (forall bP : anf pv bare, agood_body cv bP) /\
  (forall eP : value pv bare, agood_rev cv eP).
Proof.
have [_ Hv] := agood_fwd cv.
apply: anf_value_ind.
- by move=> a e IHe b IHb; apply: agood_body_let.
- by move=> a; apply: agood_body_ret.
- by move=> f a; apply: agood_rev_op1.
- by move=> f a b; apply: agood_rev_op2.
- by move=> a i; apply: agood_rev_get.
- by move=> a i v; apply: agood_rev_set.
- by move=> c t IHt e IHe; apply: agood_rev_ite.
- by move=> lo hi b IHb; apply: agood_rev_map.
by move=> a lo hi init b IHb; apply: agood_rev_fold.
Qed.

End AGoodRev.
