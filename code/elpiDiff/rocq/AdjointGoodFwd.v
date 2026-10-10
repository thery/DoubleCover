(* AdjointGoodFwd.v — the forward sweep of the adjoint code keeps the
   scoping discipline (AdjointGood.v): prim and fwd_value, for every body
   and every value, by induction on the syntax, as TangentGood.v does for
   the tangent code.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops
  TangentGood AdjointCorrect AdjointBranch AdjointGood.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section AGoodFwd.
Variable cv : bool.

(* An atom whose variable is in scope, spelled. *)
Lemma atom_scope L k c wP pp (live : pv -> Prop) ty sc wr (aP : atom pv) :
  sctx L k c wP pp live ty -> fscope L c wP pp live sc wr ->
  (forall p, aP = AVar p -> In p L /\ live p) ->
  expr_ok sc (spell (amap pt aP)).
Proof.
move=> Hs [_ [_ [Hr _]]]; case: aP => [p | |] H //=.
have [Hp Lp] := H p erefl.
have [_ [_ [Hst _]]] := static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp.
by rewrite Hst; exact: Hr.
Qed.

(* A body that returns an atom: no statement. *)
Lemma agood_ret (aP : atom pv) : agood_prim cv (ARet aP).
Proof.
move=> L k c wP pp m m' [? ? ? | aA] [? ? ? | aW] [? ? ? | aT] //= ty sc wr.
move=> HA HW HT Hs Hsc _ _.
case/atom_graph: HT => -> HT; case/atom_graph: HW => EW HW; subst aW.
split=> //; apply: good_k_nil; [by case: Hsc | by case: Hsc => _ [] |].
apply: (atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc) => p E; split; first exact: HT.
by subst aP; rewrite /live_anf /= Nat.eqb_refl.
Qed.

Ltac avalue_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in
  intros L k c wP pp m tail eA eW eT te n rec ty sc wr HA HW HT Hs Hsc Htp
    Htc Htail [j [Ej Hj]] Hst Hrec;
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

(* The definition of the constant n that a value computes: n is in scope
   after it. *)
Lemma good_value_const j c sc wr (t : ty) e (Q : list (dvar W) -> Prop) :
  expr_ok sc e -> ~ In (DBound (j, j)) sc -> (j < c)%nat ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc -> Q wr ->
  good_k sc wr c [DDefine (DConstant t) (DBound (j, j)) e]
    (fun sc' wr' =>
       In (DBound (j, j)) sc' /\
       (forall x, In x sc' ->
          In x sc \/ x = DBound (j, j) \/ x = TapeOf (DBound (j, j))) /\
       Q wr').
Proof.
move=> He Hn Hj Hb Hw HQ; apply: good_constant => //.
split; first by left.
by split=> // x [<- | Hx]; auto.
Qed.

Lemma agood_op1 f (aP : atom pv) : agood_value cv (AOp1 f aP).
Proof.
avalue_intro.
rewrite /= in Hst *; case: Hst => N1 _.
split=> //; apply: good_value_const => //; try by case: Hsc => ? [].
rewrite /=; apply: (atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc) => p E.
by subst aP; split; [auto | rewrite /live_value /= Nat.eqb_refl].
Qed.

Lemma agood_op2 f (aP bP : atom pv) : agood_value cv (AOp2 f aP bP).
Proof.
avalue_intro.
rewrite /= in Hst *; case: Hst => N1 _.
split=> //; apply: good_value_const => //; try by case: Hsc => ? [].
rewrite /=; split; apply: (atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc) => p E;
  subst; split; auto; rewrite /live_value /= Nat.eqb_refl ?orb_true_r //.
Qed.

Lemma agood_get (aP iP : atom pv) : agood_value cv (AGet aP iP).
Proof.
avalue_intro.
rewrite /= in Hst *; case: Hst => N1 _.
split=> //; apply: good_value_const => //; try by case: Hsc => ? [].
rewrite /=; split; apply: (atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc) => p E;
  subst; split; auto; rewrite /live_value /= Nat.eqb_refl ?orb_true_r //.
Qed.

Lemma agood_set (aP iP vP : atom pv) : agood_value cv (ASet aP iP vP).
Proof.
avalue_intro.
rewrite /= in Htc *.
destruct pp as [| | | ix sx]; rewrite /= in Htc; try discriminate.
move: Htc; case Eat: (of_atom (amap pw aP)) => [| | | z] // Htc.
destruct tail; rewrite /= in Htc; last discriminate.
destruct aP as [a | |]; rewrite /= in Htc Eat; try discriminate.
move: Htc; case Ea: (vid (pw a) =? vid (pw sx))%nat => //= Htc.
have [Hix [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
have Ha : In a L by auto.
have Eas := same_vid_s _ _ _ _ _ _ _ _ _ Hs Ha Hsx Ea; subst a.
rewrite /= in Hst; case: Hst => Ej; subst j.
have [Hb [Hw [_ Ho]]] := Hsc.
have W1 := Ho sx erefl.
have Hlv : forall p, iP = AVar p \/ vP = AVar p ->
    In p L /\
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p.
  by move=> p [E | E]; subst; split; auto;
    rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
have I1 := atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc
  (fun p E => Hlv p (or_introl E)).
have V1 := atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc
  (fun p E => Hlv p (or_intror E)).
move=> _.
have Hn : In (DBound (pn sx, pn sx)) wr by exact: W1.
have Hel : expr_ok sc
    (DAt (DVar (DBound (pn sx, pn sx))) (spell (amap pt iP))).
  by split; [apply: Hw | exact: I1].
case Er: (sweep_eqb m Forward && rec) => /=; split=> // rest Hrest.
  move/andP: Er => [Em Er].
  have [_ Ht] := Hrec Er.
  apply: GoodPush; [exact: Ht Em | exact: Hel |].
  apply: GoodAssign; [split; [exact: Hn | exact: I1] | exact: V1 |].
  apply: (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw).
  by split; [apply: Hw | split=> // x Hx; left].
apply: GoodAssign; [split; [exact: Hn | exact: I1] | exact: V1 |].
apply: (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw).
by split; [apply: Hw | split=> // x Hx; left].
Qed.

(* The variable whose storage a value updates in place: the array it sets,
   the state of its in-place fold, the array its map writes. *)
Definition stor_var (wP : option (atom pv)) (eP : value pv bare) (q : pv) :
  Prop :=
  match eP with
  | ASet (AVar a) _ _ => a = q
  | AFold _ _ _ (AVar i) _ => i = q
  | AMap _ _ _ => wP = Some (AVar q)
  | _ => False
  end.

(* open_with_storage', with the variable of the storage. *)
Lemma open_with_storage_v {A : Type} L k wP (eP : value pv bare) eT vt
  (bT : tvar W -> anf (tvar W) ann) (K : dvar W -> bool -> scoped W A) c :
  value_eq (gT L) eP eT -> Forall (static_ok k) L ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L) ->
  exists n rec c0,
    open_pairs (with_storage (option_map (amap pt) wP)
                  (rebuild_value _ eT vt) bT K) c =
    open_pairs (K n rec) c0 /\
    match storage wP (Transform.is_tail bT) eP with
    | Some m =>
        n = m /\ c0 = c /\
        exists q, In q L /\ stored q = m /\ rec = trecorded (pt q) /\
                  stor_var wP eP q
    | None => n = DBound (c, c) /\ c0 = S c /\ rec = false
    end.
Proof.
move=> HT HL Hw.
have Hst : forall p, In p L ->
    tstored (pt p) = stored p /\ tty (pt p) = vty (pw p).
  by move=> p Hp; have [_ [_ [H1 [H2 _]]]] := static_in _ _ _ HL Hp.
Local Ltac fresh_case_v :=
  solve [eexists (DBound (_, _)), false, (S _); simpl; auto].
destruct eP as
  [f a | f a b | a i | a i x | cnd t e | lo hi b | an lo hi init b], eT;
  simpl in HT; try contradiction; simpl;
  try fresh_case_v; try (destruct vt; fresh_case_v).
- case: HT => Ha _; destruct a as [p | |]; destruct a0; simpl in Ha;
    try contradiction; try fresh_case_v.
  case/in_gT: Ha => Hp ->; have [E _] := Hst _ Hp.
  exists (stored p), (trecorded (pt p)), c; rewrite /= E.
  by split=> //; split=> //; split=> //; exists p.
- destruct vt; simpl;
    (destruct (Transform.is_tail bT); [| fresh_case_v]);
    (destruct wP as [[y | |] |]; simpl;
     [| fresh_case_v | fresh_case_v | fresh_case_v]);
    (destruct (Hw _ eq_refl) as [y' [E Hy]]; injection E as <-;
     destruct (Hst _ Hy) as [E _]; exists (stored y), (trecorded (pt y)), c;
     rewrite E; split; [reflexivity | split; [reflexivity |
       split; [reflexivity | exists y; auto]]]).
case: HT => _ [_ [Hi _]]; destruct init as [p | |], init0; simpl in Hi;
  try contradiction; destruct vt; simpl; try fresh_case_v;
  (apply in_gT in Hi as [Hp ->]; destruct (Hst _ Hp) as [E1 E2]; rewrite E2;
   destruct (vty (pw p)); try fresh_case_v;
   exists (stored p), (trecorded (pt p)), c; rewrite E1;
   split; [reflexivity | split; [reflexivity |
     split; [reflexivity | exists p; auto]]]).
Qed.

(* The storage of a value updated in place is the one of the owner. *)
Lemma stor_owner L k c wP pp ty tail (eP : value pv bare) eW te q o :
  sctx L k c wP pp (live_value k eW) ty -> value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW =
    (te, Ok) ->
  In q L -> stored q = stored o -> owner wP pp = Some o ->
  stor_var wP eP q -> q = o.
Proof.
move=> Hs HW Htc Hq Eqo Ho.
have Epn : pn q = pn o by case: Eqo.
have Hlv : live_value k eW q -> q = o.
  by move=> Hl; case: (s_owner _ _ _ _ _ _ _ Hs o q Ho Hq Epn).
destruct eP as [f a | f a b | a i | a i v | cnd t e | lo hi b
               | an lo hi i b], eW;
  rewrite /= in HW; try contradiction; rewrite /=; try by [].
- case: a HW => [a | |] //= [Ha _] Eaq; subst a; apply: Hlv.
  destruct a0 as [w | |]; rewrite /= in Ha; try contradiction.
  move/in_gW: Ha => [_ ->].
  by rewrite /live_value /= Nat.eqb_refl.
- move=> Ew; destruct pp as [| | | ix sx]; rewrite /= in Htc;
    try discriminate.
  by move: Ho; rewrite Ew /=; case: (vty (pw q)) => // ? [].
case: i HW => [i | |] // [_ [_ [Hi _]]] Eiq; subst i; apply: Hlv.
destruct init as [w | |]; rewrite /= in Hi; try contradiction.
move/in_gW: Hi => [_ ->].
by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
Qed.

Lemma fscope_weaken L c c' wP pp (rd rd' : pv -> Prop) sc wr :
  fscope L c wP pp rd sc wr -> (forall p, In p L -> rd' p -> rd p) ->
  (c <= c')%nat -> fscope L c' wP pp rd' sc wr.
Proof.
move=> [Hb [Hw [Hr Ho]]] Hl Hc; split.
  apply: (Forall_impl _ _ Hb) => x [H1 H2]; split=> //.
  exact: (below_mono _ _ _ H1 Hc).
by split=> //; split=> // p Hp Lp; apply: Hr; auto.
Qed.

Lemma tape_fwd_mono wP pp m (rr rr' : bool) sc wr :
  tape_fwd wP pp m rr sc wr -> (rr' = true -> rr = true) ->
  tape_fwd wP pp m rr' sc wr.
Proof.
move=> Ht Hr o Ho; have [T1 T3] := Ht o Ho.
split=> // Hl; have [T4 T5] := T3 Hl; split=> // /andP [Hm Ho'].
apply: T5; rewrite Hm /=.
by case/orP: Ho' => [-> | /Hr ->] //; rewrite orb_true_r.
Qed.

(* The tape condition, after a value computed into n, a fresh variable. *)
Lemma tape_fwd_ext wP pp m rr sc wr sc1 wr1 j :
  tape_fwd wP pp m rr sc wr -> incl wr wr1 ->
  (forall x, In x sc1 ->
     In x sc \/ x = DBound (j, j) \/ x = TapeOf (DBound (j, j))) ->
  (forall o, owner wP pp = Some o -> stored o <> DBound (j, j)) ->
  tape_fwd wP pp m rr sc1 wr1.
Proof.
move=> Ht Hw Hs Hn o Ho; have [T1 T2] := Ht o Ho; split.
  move=> Hl; have [T3 T4] := T1 Hl; split=> //.
  move=> /Hs [| [E | [E]]] //.
  by move=> E'; apply: (Hn o Ho); rewrite /stored E'.
by move=> Hl; have [T3 T4] := T2 Hl; split=> // Hm; apply/Hw/T4.
Qed.

Lemma agood_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  agood_value cv eP -> (forall x, agood_prim cv (cP x)) ->
  agood_prim cv (ALet a eP cP).
Proof.
move=> IHe IHb L k c wP pp m m' bA bW bT ty sc wr HA HW HT Hs Hsc Htp Htc.
destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |];
  rewrite /= in HA HW HT; try contradiction.
case: HA => HeA HcA; case: HW => HeW HcW; case: HT => HeT HcT.
rewrite /= in Htc; move: Htc.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
             (WellFormed.is_tail cW k) k eW) => [te d0].
case: d0 Hte => [| msg] Hte /= Htc //.
cbn [annotate_body_t].
case: (needs cv m' (S k) (cA (let_binder k eA))) => u l.
set vr := varied_value k eA; set vt := annotate_value_t cv k eA.
set rest := annotate_body_t cv m' (S k) (cA (let_binder k eA)).
cbn [rebuild]; rewrite prim_let; cbv [let_ann].
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
set Kf := (X in with_storage _ _ _ X).
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
case Hse: (open_pairs (fwd_value _ _ _ _ _ _ _) c0) => [se c1].
have Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by move=> p H; rewrite /live_value /live_anf /= in H *; rewrite H.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Hs0 : sctx L k c wP pp (live_value k eW) ty.
  exact: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e (le_n c)).
have [Hb [Hw [Hr Ho]]] := Hsc.
(* the storage, and the number of n *)
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
have Hst : match storage wP tail eP return Prop with
           | Some m0 => n = m0
           | None => ~ In n sc /\ ~ In (TapeOf n) sc
           end.
  case: (storage wP tail eP) Hn Hjs => [m0 | ] Hn Hjs; first by case: Hn.
  subst j; rewrite Ej.
  by split=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _];
    rewrite /= in Hbl; lia.
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
(* the value *)
have Hsc0 : fscope L c0 wP pp (live_value k eW) sc wr.
  apply: (fscope_weaken _ _ _ _ _ _ _ _ _ Hsc _ Hc0) => p _.
  exact: Hlive_e.
have Htp0 : tape_fwd wP pp m (records cv k eA) sc wr.
  by apply: (tape_fwd_mono _ _ _ _ _ _ _ Htp); rewrite /= => ->.
have IH0 := IHe L k c0 wP pp m tail eA eW eT te n rec ty sc wr HeA HeW HeT
  (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hc0) Hsc0 Htp0 Hte Htail_ty
  (ex_intro _ j (conj Ej Hj0)) Hst Hrec.
cbv zeta in IH0; rewrite -/vt Hse in IH0.
case: IH0 => Hc01 Hgk1.
(* the variable of the let *)
set x := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec)
           (default_dual te) j.
have Hx : aid (pa x) = k by [].
have HxL : ~ In x L := fresh_notin L k x (aids_below L k HL) Hx.
have Hvid : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [_ [H _]] := static_in _ _ _ HL Hp.
rewrite open_pairs_sbind.
case Es: (storage wP tail eP) Hn Hst Hjs => [m0 |] Hn Hst Hjs.
  (* stored in place: the rest only returns the variable *)
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [Ht [o [Ho' Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
  have ET : cT (pt x) = ARet (AVar (pt x)).
    move: (HcT x (pt x)); rewrite Hcx.
    case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gT: I => I _.
  rewrite /= in ET; rewrite ET /=.
  split; first lia.
  rewrite app_nil_r => rest' Hrest.
  by apply: Hgk1 => sc1 wr1 I1 I2 Hb1 Hw1 [Q1 _]; apply: Hrest.
(* a fresh variable *)
case: Hn => En [Ec0 Erec]; subst n j rec.
have Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
    live_anf k (ALet aW eW cW) p.
  rewrite /live_anf => p Hp H /=.
  rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx erefl) in H.
  by rewrite H orb_true_r.
set cW' := cW (VInfo k te None).
have Hxs : static_ok (S k) x.
  have [D1 D2] := default_dual_ok te.
  repeat split; rewrite /=; auto; try lia; try discriminate.
  move=> Hv.
  exact: (varied_real_or_array _ _ _ _ _ _ _ _ _ HeA HeW HL Hte Hv).
have Hs' : sctx (x :: L) (S k) c1 wP pp (live_anf (S k) cW') ty.
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
  - have Hp := s_place _ _ _ _ _ _ _ Hs; destruct pp; simpl in Hp |- *; auto.
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
have Hpo : forall o, owner wP pp = Some o -> stored o <> DBound (c, c).
  move=> o Ho' [E _].
  have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho').
  by rewrite E; lia.
have Hsc' : forall sc1 wr1, incl sc sc1 -> incl wr wr1 ->
    Forall (fun y => below c1 y /\ consistent y) sc1 -> incl wr1 sc1 ->
    In (DBound (c, c)) sc1 ->
    fscope (x :: L) c1 wP pp (live_anf (S k) cW') sc1 wr1.
  move=> sc1 wr1 I1 I2 Hb1 Hw1 Q1; split=> //; split=> //; split.
    move=> p [<- | Hp] Hl; first exact: Q1.
    by apply: I1; apply: Hr Hp (Hlive_c p Hp Hl).
  by move=> o Ho'; apply: I2; apply: Ho.
have Htp' : forall sc1 wr1, incl wr wr1 ->
    (forall y, In y sc1 ->
       In y sc \/ y = DBound (c, c) \/ y = TapeOf (DBound (c, c))) ->
    tape_fwd wP pp m (records_in cv (S k) (cA (pa x))) sc1 wr1.
  move=> sc1 wr1 I2 Hy.
  apply: (tape_fwd_ext _ _ _ _ _ _ _ _ _ _ I2 Hy Hpo).
  apply: (tape_fwd_mono _ _ _ _ _ _ _ Htp) => H /=.
  by rewrite H orb_true_r.
(* the rest of the body *)
case Hsb: (open_pairs (prim W (option_map (amap pt) wP) m
             (rebuild (tvar W) (cT (open_let te (DBound (c, c)) vr false))
                rest)) c1) => [[sb x'] c2] /=.
have Hcons : Forall (fun y => below c1 y /\ consistent y)
               (DBound (c, c) :: sc).
  constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [H1 H2]; split=> //.
  by apply: (below_mono c); [exact: H1 | lia].
have Hi0 : incl sc (DBound (c, c) :: sc) by move=> y Hy; right.
have Hw0 : incl wr (DBound (c, c) :: sc) by move=> y Hy; right; apply: Hw.
have Hy0 : forall y, In y (DBound (c, c) :: sc) ->
    In y sc \/ y = DBound (c, c) \/ y = TapeOf (DBound (c, c)).
  by move=> y [<- | Hy]; auto.
have IH0 := IHb x (x :: L) (S k) c1 wP pp m m' (cA (pa x)) cW' (cT (pt x))
  ty (DBound (c, c) :: sc) wr (HcA x _) (HcW x _) (HcT x _) Hs'
  (Hsc' _ _ Hi0 (incl_refl _) Hcons Hw0 (or_introl erefl))
  (Htp' _ _ (incl_refl _) Hy0) Htc.
rewrite /x in IH0; cbn [pt pa] in IH0; rewrite -/rest Hsb in IH0.
case: IH0 => Hc12 _.
split; first lia.
apply: (good_k_app sc wr c1 c2 se sb _ _ Hgk1).
move=> sc1 wr1 I1 I2 Hb1 Hw1 [Q1 [Q2 _]].
have IH1 := IHb x (x :: L) (S k) c1 wP pp m m' (cA (pa x)) cW' (cT (pt x))
  ty sc1 wr1 (HcA x _) (HcW x _) (HcT x _) Hs'
  (Hsc' _ _ I1 I2 Hb1 Hw1 Q1) (Htp' _ _ I2 Q2) Htc.
rewrite /x in IH1; cbn [pt pa] in IH1; rewrite -/rest Hsb in IH1.
exact: (proj2 IH1).
Qed.

Lemma agood_ite (cP : atom pv) (tP eP : anf pv bare) :
  agood_prim cv tP -> agood_prim cv eP -> agood_value cv (AIte cP tP eP).
Proof.
move=> IHt IHe.
avalue_intro.
rewrite /= in Htc Hst *.
rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT.
rename H6 into HAt, H7 into HAe, H3 into HWt, H4 into HWe, H0 into HTt,
  H1 into HTe.
have Hnot : forall ix sx, pp <> PArray ix sx.
  by move=> ix sx E; rewrite E /= in Htc.
have Hpp : pp = PTop \/ pp = PBranch \/ pp = PScalar.
  by destruct pp as [| | | ix sx]; auto; case: (Hnot ix sx erefl).
have Htc' : (if ty_eqb (of_atom (amap pw cP)) Boolean
             then let '(t3, d1) :=
                    typecheck (option_map (amap pw) wP) InBranch k tW in
                  let '(t4, d2) :=
                    typecheck (option_map (amap pw) wP) InBranch k eW in
                  if is_ok d1 then if is_ok d2 then
                    if ty_eqb t3 Real && ty_eqb t4 Real then (Real, Ok)
                    else (Real, Error "both branches must compute a real")
                  else (Real, d2) else (Real, d1)
             else (Real, Error "a branch condition must be a comparison")) =
            (te, Ok).
  by move: Htc; case: Hpp => [-> | [-> | ->]].
clear Htc.
move: Htc'; case Ecb: (ty_eqb (of_atom (amap pw cP)) Boolean) => // Htc'.
case HtW: (typecheck (option_map (amap pw) wP) InBranch k tW) Htc'
  => [t3 d1] Htc'.
case HeW: (typecheck (option_map (amap pw) wP) InBranch k eW) Htc'
  => [t4 d2] Htc'.
destruct d1, d2; rewrite /= in Htc'; try discriminate.
move: Htc'; case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= Htc'.
case: Htc' => Ete; subst te.
move/ty_eqb_true: E3 => E3; move/ty_eqb_true: E4 => E4; subst t3 t4.
case: Hst => N1 _.
have C1 : expr_ok sc (spell (amap pt cP)).
  apply: (atom_scope _ _ _ _ _ _ _ _ _ _ Hs Hsc) => p E.
  by subst cP; split; [auto | rewrite /live_value /= Nat.eqb_refl].
have [Hb [Hw [Hr Ho]]] := Hsc.
(* the two bodies, opened *)
rewrite open_pairs_sbind.
case Hot: (open_pairs (prim W (option_map (amap pt) wP) m
             (rebuild (tvar W) tT (annotate_body_t cv Replay k tA))) c)
  => [[st vt] c1].
rewrite open_pairs_sbind.
case Hoe: (open_pairs (prim W (option_map (amap pt) wP) m
             (rebuild (tvar W) eT (annotate_body_t cv Replay k eA))) c1)
  => [[se' ve'] c2].
cbn zeta; rewrite /=.
set n := DBound (j, j) in N1 *.
have Hb2 : forall c', (c <= c')%nat ->
    Forall (fun x => below c' x /\ consistent x) (n :: sc).
  move=> c' Hc'; constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  exact: (below_mono _ _ _ Y1 Hc').
have Hwr2 : incl (n :: wr) (n :: sc).
  by move=> y [<- | Hy]; [left | right; apply: Hw].
(* a branch body *)
have Hbr : forall bP bA bW bT (cb cb' : nat) sb vb,
    anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
    agood_prim cv bP -> (c <= cb)%nat ->
    (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
    typecheck (option_map (amap pw) wP) InBranch k bW = (Real, Ok) ->
    open_pairs (prim W (option_map (amap pt) wP) m
                  (rebuild (tvar W) bT (annotate_body_t cv Replay k bA))) cb
      = ((sb, vb), cb') ->
    (cb <= cb')%nat /\ good (n :: sc) (n :: wr) (sb ++ [DAssign (DVar n) vb]).
  move=> bP bA bW bT cb cb' sb vb HA' HW' HT' IH Hcb Hl Htb Hob.
  have Hs' : sctx L k cb wP PBranch (live_anf k bW) Real.
    apply: (sctx_sub L k cb wP pp PBranch
              (live_value k (AIte (amap pw cP) tW eW)) _ ty) => //.
    by apply: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs); auto.
  have Hsc' : fscope L cb wP PBranch (live_anf k bW) (n :: sc) (n :: wr).
    split; first exact: (Hb2 _ Hcb).
    split; first exact: Hwr2.
    split; last by move=> o E.
    by move=> p Hp Lp; right; apply: Hr Hp (Hl p Lp).
  have Htp' : tape_fwd wP PBranch m (records_in cv k bA) (n :: sc) (n :: wr).
    by move=> o E.
  have := IH L k cb wP PBranch m Replay bA bW bT Real (n :: sc) (n :: wr)
            HA' HW' HT' Hs' Hsc' Htp' Htb.
  rewrite Hob => -[Hc' Hg].
  split; first exact: Hc'.
  apply: Hg => sc' wr' I1 I2 _ _ Q1.
  by apply: GoodAssign; [apply: I2; left | exact: Q1 | constructor].
have Hlt : forall p, live_anf k tW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' orb_true_r.
have Hle : forall p, live_anf k eW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' !orb_true_r.
have [Hc1 Hg1] :=
  Hbr tP tA tW tT c c1 st vt HAt HWt HTt IHt (le_n c) Hlt HtW Hot.
have [Hc2 Hg2] :=
  Hbr eP eA eW eT c1 c2 se' ve' HAe HWe HTe IHe Hc1 Hle HeW Hoe.
split; first lia.
move=> rest Hrest.
apply: GoodRealVar; [exact: N1 | by [] |].
have Hc : expr_ok (n :: sc) (spell (amap pt cP)).
  by apply: (expr_ok_incl sc) C1 => y Hy; right.
apply: GoodBranch; [exact: Hc | exact: Hg1 | exact: Hg2 |].
apply: Hrest; [by move=> y Hy; right | by move=> y Hy; right |
               apply: Hb2; lia | exact: Hwr2 |].
split; first by left.
by split=> // x [<- | Hx]; auto.
Qed.

Lemma agood_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, agood_prim cv (bP x)) -> agood_value cv (AMap loP hiP bP).
Proof.
move=> IHb.
avalue_intro.
rewrite /= in Htc *.
rename b into bA, b0 into bW, b1 into bT.
match goal with H : forall (i1 : pv) (i2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with H : forall (i1 : pv) (i2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with H : forall (i1 : pv) (i2 : tvar W), _ |- _ =>
  rename H into HbT end.
have HL := s_static _ _ _ _ _ _ _ Hs.
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
rewrite /= in Hst; case: Hst => Ej; subst j.
have HtB : typecheck (Some (AVar (pw o))) ScalarBody (S k)
             (bW (VInfo k Integer None)) = (Real, Ok).
  move: Htc => /=; case: (varg (pw o)) => [[nm [] ] |] /=;
    case: (occurs_anf (vid (pw o)) (S k) (bW (anon k))) => //;
    case: (typecheck (Some (AVar (pw o))) ScalarBody (S k)
             (bW (VInfo k Integer None))) => [tb [| mm]] //=;
    by case Etb: (ty_eqb tb Real) => // _; move/ty_eqb_true: Etb => ->.
have [o'' [[Eo''] [HoL _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
subst o''.
have Hown : owner (Some (AVar o)) PTop = Some o by rewrite /= Ey.
have [Hb [Hw [Hr Ho]]] := Hsc.
have W1 := Ho o Hown.
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb vb] c2].
cbn [open_pairs spell amap].
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
have Hlive_b : forall p, In p L ->
    live_anf (S k) (bW (VInfo k Integer None)) p ->
    live_value k (AMap (ANat 0) (ANat h) bW) p.
  move=> p Hp Hl; rewrite /live_anf /live_value /= in Hl *.
  by rewrite -(live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ HbW HL
                erefl erefl).
have Hcons : Forall (fun x => below (S c) x /\ consistent x)
               (DBound (c, c) :: sc).
  constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
have Hsc' : fscope (ix :: L) (S c) (Some (AVar o)) PScalar
              (live_anf (S k) (bW (VInfo k Integer None)))
              (DBound (c, c) :: sc) wr.
  split; first exact: Hcons.
  split; first by move=> y Hy; right; apply: Hw.
  split; last by move=> o' E.
  move=> p [<- | Hp] Lp; first by left.
  by right; apply: Hr Hp (Hlive_b p Hp Lp).
have Htp' : tape_fwd (Some (AVar o)) PScalar m
    (records_in cv (S k) (bA (fresh k))) (DBound (c, c) :: sc) wr.
  by move=> o' E.
have := IHb ix (ix :: L) (S k) (S c) (Some (AVar o)) PScalar m Replay
          (bA (fresh k)) (bW (VInfo k Integer None))
          (bT (open_index (DBound (c, c)))) Real (DBound (c, c) :: sc) wr
          (HbA ix _) (HbW ix _) (HbT ix _) Hs' Hsc' Htp' HtB.
rewrite Hob => -[Hc2 Hg].
split; first lia.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
have Hb2 : Forall (fun x => below c2 x /\ consistent x) sc.
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
move=> rest Hrest /=.
apply: GoodFor; [exact: Hni | by [] | exact I | exact I | |].
  apply: Hg => sc' wr' I1 I2 _ _ Q1.
  apply: GoodAssign;
    [split; [apply: I2; exact: W1 | by apply: I1; left] | exact: Q1 |].
  by constructor.
apply: Hrest; [exact: incl_refl | exact: incl_refl | exact: Hb2 | exact: Hw |].
split; first by apply: Hw.
split; first by move=> x Hx; left.
by rewrite andb_false_r.
Qed.

(* The written argument is the storage of the in-place fold at the top: its
   tape is declared there, not in the body of an in-place loop. *)
Lemma is_written_none (w : option (atom (tvar W))) (x : tvar W) :
  tid x = None -> is_written w (AVar x) = false.
Proof. by move=> E; case: w => [[y | |] |] //=; rewrite /is_written E. Qed.

Lemma is_written_top wP o :
  owner wP PTop = Some o -> tid (pt o) <> None ->
  is_written (option_map (amap pt) wP) (AVar (pt o)) = true.
Proof.
case: wP => [[y | |] |] //=; case: (vty (pw y)) => // ? [<-] H.
by rewrite /is_written; case: (tid (pt y)) H => // t _; rewrite Nat.eqb_refl.
Qed.

Lemma not_in_loop_dec pp : not_in_loop pp \/ ~ not_in_loop pp.
Proof. by case: pp => *; [left | left | left | right]. Qed.

Lemma agood_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall x y, agood_prim cv (bP x y)) ->
  agood_value cv (AFold a loP hiP initP bP).
Proof.
move=> IHb.
avalue_intro.
rewrite /= in Htc *.
rename b into bA, b0 into bW, b1 into bT.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ =>
  rename H into HbT end.
have HL := s_static _ _ _ _ _ _ _ Hs.
move: Htc; case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
                     ty_eqb (of_atom (amap pw hiP)) Integer) => // Htc.
have Hlv : forall p, loP = AVar p \/ hiP = AVar p \/ initP = AVar p ->
    In p L /\
    live_value k (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
  by move=> p [E | [E | E]]; subst; split; auto;
    rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
have L1 := atom_scope _ _ _ _ _ _ _ _ _ loP Hs Hsc
  (fun p E => Hlv p (or_introl E)).
have H1' := atom_scope _ _ _ _ _ _ _ _ _ hiP Hs Hsc
  (fun p E => Hlv p (or_intror (or_introl E))).
have I1 := atom_scope _ _ _ _ _ _ _ _ _ initP Hs Hsc
  (fun p E => Hlv p (or_intror (or_intror E))).
have [Hb [Hw [Hr Ho]]] := Hsc.
set svr := fold_varied k (amap pa initP) bA.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
cbn [annotate_value_t rebuild_value fold_binders fold_ann].
move: Htc; case Er: (ty_eqb (of_atom (amap pw initP)) Real) => Htc.
  (* a real state, at the top *)
  move/ty_eqb_true: Er => Er.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Htc; try discriminate.
  case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
              (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
    => [tb [| mm]] Htc; rewrite /= in Htc; try discriminate.
  case Etb: (ty_eqb tb Real) Htc => Htc; rewrite /= in Htc; try discriminate.
  move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => Ete; subst te.
  have Hs0 : storage wP tail (AFold a loP hiP initP bP) = None.
    by destruct initP as [q | |]; rewrite /= in Er *; rewrite ?Er.
  rewrite Hs0 in Hst; case: Hst => N1 N2.
  cbn [open_pairs].
  rewrite open_pairs_sbind.
  case Hob: (open_pairs _ (S c)) => [[sb vb] c2].
  cbn [open_pairs].
  set live := sweep_eqb m Forward && state_live cv k (amap pa initP) bA.
  set n := DBound (j, j) in N1 N2 Hob *.
  set ix := PV (AV k false) (VInfo k Integer None)
              (TVar (DBound (c, c)) Integer None false false false false None)
              (VInt 0) c.
  set sx := PV (AV (S k) svr) (VInfo (S k) Real None)
              (TVar n Real None svr svr svr false None) (VReal (Dual 0 0)) j.
  set sc2 := if live then TapeOf n :: n :: sc else n :: sc.
  set wr2 := if live then TapeOf n :: n :: wr else n :: wr.
  have Hsc2 : incl sc sc2 by rewrite /sc2; case: (live) => y Hy /=; auto.
  have Hwr2 : incl wr2 sc2.
    by rewrite /sc2 /wr2; case: (live) => y /= Hy; intuition.
  have Hn2 : In n sc2 /\ In n wr2.
    by rewrite /sc2 /wr2; case: (live) => /=; auto.
  have Hb2 : forall c', (c <= c')%nat ->
      Forall (fun x => below c' x /\ consistent x) sc2.
    move=> c' Hc'; rewrite /sc2.
    have Hbc : Forall (fun x => below c' x /\ consistent x) sc.
      apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
      exact: (below_mono _ _ _ Y1 Hc').
    by case: (live); repeat constructor; auto; rewrite /=; lia.
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k))
        (bW (VInfo k Integer None) (VInfo (S k) Real None)) p ->
      live_value k
        (AFold ann0 (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
    move=> p Hp Hl; rewrite /live_anf /live_value /= in Hl *.
    by rewrite -(live_cont2 L k bP bW (pfresh k) (pfresh (S k))
                  (VInfo k Integer None) (VInfo (S k) Real None)
                  _ HbW HL erefl erefl erefl erefl) Hl !orb_true_r.
  have Hs' : sctx (sx :: ix :: L) (S (S k)) (S c) wP PScalar
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      Real.
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
  have Hsc' : fscope (sx :: ix :: L) (S c) wP PScalar
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      (DBound (c, c) :: sc2) wr2.
    split.
      by constructor; [split=> /=; [lia | by []] | apply: Hb2; lia].
    split; first by move=> y Hy; right; apply: Hwr2.
    split; last by move=> o E.
    move=> p [<- | [<- | Hp]] Lp; first by right; exact: (proj1 Hn2).
      by left.
    by right; apply: Hsc2; apply: Hr Hp (Hlive_b p Hp Lp).
  have Htp' : tape_fwd wP PScalar m
      (records_in cv (S (S k)) (bA (pa ix) (pa sx))) (DBound (c, c) :: sc2)
      wr2 by move=> o E.
  have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) wP PScalar m Replay
            (bA (pa ix) (pa sx))
            (bW (VInfo k Integer None) (VInfo (S k) Real None))
            (bT (pt ix) (pt sx)) Real (DBound (c, c) :: sc2) wr2
            (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) Hs' Hsc' Htp' HtB.
  rewrite Hob => -[Hc2 Hg].
  have Hbody : good (DBound (c, c) :: sc2) wr2
      (sb ++ [DAssign (DVar n) vb]).
    apply: Hg => sc' wr' J1 J2 _ _ Q1.
    by apply: GoodAssign; [apply: J2; exact: (proj2 Hn2) | exact: Q1 |
                           constructor].
  have Hin2 : ~ In (DBound (c, c)) sc2.
    rewrite /sc2 /n; case: (live) => /= Hin;
      repeat match type of Hin with _ \/ _ =>
        destruct Hin as [E | Hin];
        [first [discriminate E | inversion E; lia] |] end;
      contradiction.
  have HL1 : expr_ok sc2 (spell (amap pt loP)) by apply: (expr_ok_incl sc).
  have HH1 : expr_ok sc2 (spell (amap pt hiP)) by apply: (expr_ok_incl sc).
  have HQ : forall wr', sweep_eqb m Forward &&
      records cv k (AFold ann (amap pa loP) (amap pa hiP) (amap pa initP) bA)
        = true -> not_in_loop PTop ->
      storage wP tail (AFold a loP hiP initP bP) <> None ->
      In (TapeOf n) wr'.
    by move=> wr' _ _; rewrite Hs0.
  split; first lia.
  move=> rest Hrest; rewrite /fwd_fold; destruct live eqn:Hlive; rewrite /=.
    apply: GoodMutable; [exact: I1 | exact: N1 | by [] |].
    apply: GoodTape; [by case=> // /N2 | by [] |].
    apply: GoodFor; [exact: Hin2 | by [] | exact: HL1 | exact: HH1 | |].
      by apply: GoodPush; [by left | by right; right; left | exact: Hbody].
    apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
                   exact: Hwr2 |].
    split; first by right; left.
    split; last exact: HQ.
    by move=> x [<- | [<- | Hx]]; auto.
  apply: GoodMutable; [exact: I1 | exact: N1 | by [] |].
  apply: GoodFor;
    [exact: Hin2 | by [] | exact: HL1 | exact: HH1 | exact: Hbody |].
  apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
                 exact: Hwr2 |].
  split; first by left.
  split; last exact: HQ.
  by move=> x [<- | Hx]; auto.
(* an array updated in place *)
case Eat: (of_atom (amap pw initP)) Htc => [| | | z] Htc //.
destruct initP as [o | | ]; rewrite /= in Eat Htc; try discriminate.
have Ho' : In o L by case: (Hlv o (or_intror (or_intror erefl))).
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
set n := DBound (pn o, pn o).
set recs := (atom_member (AVar (AV (S k) svr))
               (needs cv Replay (S (S k)) (bA (AV k false) (AV (S k) svr))).2
             || records_in cv (S (S k)) (bA (AV k false) (AV (S k) svr))).
have Erecs : records cv k (AFold ann (amap pa loP) (amap pa hiP)
               (amap pa (AVar o)) bA) = recs by [].
have Hlr : state_live cv k (amap pa (AVar o)) bA = true -> recs = true.
  by rewrite /state_live /recs /= => ->.
have Hbr :
    records_in cv (S (S k)) (bA (AV k false) (AV (S k) svr)) = true ->
    recs = true.
  by rewrite /recs => ->; rewrite orb_true_r.
have [T1 T2] := Htp o Hown; rewrite Erecs in T2.
have W1 : In n wr by exact: Ho o Hown.
set rs := sweep_eqb m Forward && state_live cv k (amap pa (AVar o)) bA || rec.
set dcl := sweep_eqb m Forward &&
           is_written (option_map (amap pt) wP) (amap pt (AVar o)) && recs.
set sc1 := if dcl then TapeOf n :: sc else sc.
set wr1 := if dcl then TapeOf n :: wr else wr.
have Hsc1 : incl sc sc1 by rewrite /sc1; case: (dcl) => y Hy /=; auto.
have Hwr1 : incl wr wr1 by rewrite /wr1; case: (dcl) => y Hy /=; auto.
have Hwr1' : incl wr1 sc1.
  by rewrite /sc1 /wr1; case: (dcl) => y /= Hy; intuition.
(* the declaration of the tape: at the top, when the fold records *)
have Hdcl : not_in_loop pp -> sweep_eqb m Forward && recs = true ->
    dcl = true.
  move=> Hl /andP [Hm Hrc]; have [T3 [T4 T5]] := T1 Hl.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hl; try done.
  by rewrite /dcl Hm Hrc (is_written_top _ _ Hown T4).
have Hndcl : ~ not_in_loop pp -> dcl = false.
  move=> Hl; have [T4 _] := T2 Hl.
  by rewrite /dcl /= (is_written_none _ _ T4) andb_false_r.
(* the tape the steps push on *)
have Htape : sweep_eqb m Forward &&
    (rs || records_in cv (S (S k)) (bA (AV k false) (AV (S k) svr))) = true ->
    In (TapeOf n) wr1.
  move=> /andP [Hm Hrr].
  case: (not_in_loop_dec pp) => Hl.
    have [T3 [T4 T5]] := T1 Hl.
    have Erec : rec = false.
      by case: (rec) Hrec => // /(_ erefl) [/(_ Hl)].
    have Ed : dcl = true.
      apply: (Hdcl Hl); rewrite Hm /=.
      move: Hrr; rewrite /rs Erec orb_false_r Hm /= => /orP [/Hlr | /Hbr] //.
    by rewrite /wr1 Ed; left.
  have [T4 T5] := T2 Hl.
  move: Hrr; rewrite /rs Hm /= -orb_assoc => /orP [Hsl | /orP [Hrc | Hbd]].
  - by apply/Hwr1/T5; rewrite Hm (Hlr Hsl) orb_true_r.
  - by apply/Hwr1; case: (Hrec Hrc) => _ /(_ Hm).
  by apply/Hwr1/T5; rewrite Hm (Hbr Hbd) orb_true_r.
have Hlivo : live_value k (AFold Bare (amap pw loP) (amap pw hiP)
                             (AVar (pw o)) bW) o.
  by case: (Hlv o (or_intror (or_intror erefl))).
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
case Hob: (open_pairs _ (S c)) => [[sb vb] c2].
cbn [open_pairs].
set ix := PV (AV k false) (VInfo k Integer None)
            (TVar (DBound (c, c)) Integer None false false false false None)
            (VInt 0) c.
set sx := PV (AV (S k) svr) (VInfo (S k) (Array z) None)
            (TVar n (Array z) None svr svr svr rs None)
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
have Hpo : (pn o < c)%nat := s_num _ _ _ _ _ _ _ Hs _ Ho'.
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
have Hb1 : forall c', (c <= c')%nat ->
    Forall (fun x => below c' x /\ consistent x) sc1.
  move=> c' Hc'.
  have Hbc : Forall (fun x => below c' x /\ consistent x) sc.
    apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
    exact: (below_mono _ _ _ Y1 Hc').
  by rewrite /sc1; case: (dcl) => //; constructor=> //; split=> /=; [lia |].
have Hcons : Forall (fun x => below (S c) x /\ consistent x)
               (DBound (c, c) :: sc1).
  by constructor; [split=> /=; [lia | by []] | apply: Hb1; lia].
have Hsc' : fscope (sx :: ix :: L) (S c) wP (PArray ix sx)
    (live_anf (S (S k)) (bW (VInfo k Integer None)
                            (VInfo (S k) (Array z) None)))
    (DBound (c, c) :: sc1) wr1.
  split; first exact: Hcons.
  split; first by move=> y Hy; right; apply: Hwr1'.
  split.
    move=> p [<- | [<- | Hp]] Lp.
    - by right; apply/Hsc1/Hw.
    - by left.
    have [Hl' _] := Hlive_b p Hp Lp.
    by right; apply/Hsc1/(Hr p Hp Hl').
  by move=> o' Ho2; rewrite /= in Ho2; case: Ho2 => Eo2; subst o';
    apply/Hwr1.
have Htp' : tape_fwd wP (PArray ix sx) m
    (records_in cv (S (S k)) (bA (pa ix) (pa sx))) (DBound (c, c) :: sc1)
    wr1.
  move=> o' Ho2; rewrite /= in Ho2; case: Ho2 => Eo2; subst o'.
  by split=> // _; split=> // Hm; apply: Htape.
have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) m Replay
          (bA (pa ix) (pa sx))
          (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
          (bT (pt ix) (pt sx)) (Array z) (DBound (c, c) :: sc1) wr1
          (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) Hs' Hsc' Htp' HtB.
rewrite Hob => -[Hc2 Hg].
have Hbody : good (DBound (c, c) :: sc1) wr1 sb.
  by rewrite -(app_nil_r sb); apply: Hg => *; constructor.
have Hin1 : ~ In (DBound (c, c)) sc1.
  by rewrite /sc1; case: (dcl) => // -[].
have HL1 : expr_ok sc1 (spell (amap pt loP)) by apply: (expr_ok_incl sc).
have HH1 : expr_ok sc1 (spell (amap pt hiP)) by apply: (expr_ok_incl sc).
split; first lia.
move=> rest Hrest.
have Hfor : good sc1 wr1
    ([DFor (DBound (c, c)) (spell (amap pt loP)) (spell (amap pt hiP)) sb]
       ++ rest).
  apply: GoodFor; [exact: Hin1 | by [] | exact: HL1 | exact: HH1 |
                   exact: Hbody |].
  apply: Hrest;
    [exact: Hsc1 | exact: Hwr1 | apply: Hb1; lia | exact: Hwr1' |].
  split; first by apply/Hsc1/Hw.
  split.
    by rewrite /sc1; case: (dcl) => x; [case=> [<- | Hx] | move=> Hx]; auto.
  move=> Hmr Hl _.
  by rewrite /wr1 (Hdcl Hl Hmr); left.
case Ed: dcl Hfor; rewrite /sc1 /wr1 Ed //= => Hfor.
apply: GoodTape => //.
case: (not_in_loop_dec pp) => Hl; first by case: (T1 Hl).
by rewrite (Hndcl Hl) in Ed.
Qed.

(* The forward sweep keeps the discipline, for every body and value. *)
Theorem agood_fwd :
  (forall bP : anf pv bare, agood_prim cv bP) /\
  (forall eP : value pv bare, agood_value cv eP).
Proof.
apply: anf_value_ind.
- by move=> a e IHe b IHb; apply: agood_let.
- by move=> a; apply: agood_ret.
- by move=> f a; apply: agood_op1.
- by move=> f a b; apply: agood_op2.
- by move=> a i; apply: agood_get.
- by move=> a i v; apply: agood_set.
- by move=> c t IHt e IHe; apply: agood_ite.
- by move=> lo hi b IHb; apply: agood_map.
by move=> a lo hi init b IHb; apply: agood_fold.
Qed.

End AGoodFwd.
