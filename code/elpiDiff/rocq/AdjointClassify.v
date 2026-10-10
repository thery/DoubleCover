(* AdjointClassify.v — a well-formed function is in the class nesty: the
   premise of adjoint_nesty_duals follows from well_formed (milestone M7).

   well_formed typechecks the vinfo instance of the normal form, with the
   binders opened at their type; nesty is about the pv instance, with any
   binders (of the type of their value, for a let). The transfer goes through
   a second pv instance b1, opened at fresh binders (fpv), related to the
   vinfo instance by gW and to the target b2 by a relation H that maps each
   binder of b1 to one of b2 (hinv): what typecheck says of b1 holds of b2.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping AnfEquiv Correctness TangentCorrect TangentLoops
  TangentGood TangentTop AdjointCorrect AdjointBranch AdjointFold AdjointFoldy
  AdjointNBody AdjointNesty.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   Fresh binders and the relation between two pv instances. *)

(* A binder opened at identity k, of type t, not varied. *)
Definition fpv (k : nat) (t : ty) : pv :=
  PV (AV k false) (VInfo k t None)
    (open_let t (DBound (k, k)) false false) (default_dual t) k.

(* H maps the variables of L, each to one variable. *)
Definition hinv (H : list (pv * pv)) (L : list pv) : Prop :=
  (forall p1 p2, In (p1, p2) H -> In p1 L) /\
  (forall p1 p2 q2, In (p1, p2) H -> In (p1, q2) H -> p2 = q2).

(* H relates variables of the same type. *)
Definition htyped (H : list (pv * pv)) : Prop :=
  forall p1 p2, In (p1, p2) H -> vty (pw p1) = vty (pw p2).

Lemma fresh_ok k t L H x2 :
  Forall (static_ok k) L -> ids_unique L -> hinv H L ->
  Forall (static_ok (S k)) (fpv k t :: L) /\ ids_unique (fpv k t :: L) /\
  hinv ((fpv k t, x2) :: H) (fpv k t :: L).
Proof.
move=> HL Hu [Hd Hf].
have Hn : ~ In (fpv k t) L.
  by apply: (fresh_notin L k _ (aids_below L k HL)).
split.
  apply: Forall_cons.
    have [D1 D2] := default_dual_ok t.
    by repeat split; rewrite /=; auto; discriminate.
  by apply: Forall_impl HL => p Hp; apply: static_mono Hp _; lia.
split.
  move=> p q [<- | Hp] [<- | Hq] //= E.
  - have [E' [Hlt _]] := static_in _ _ _ HL Hq; lia.
  - have [E' [Hlt _]] := static_in _ _ _ HL Hp; lia.
  exact: Hu.
split.
  move=> p1 p2 [[<- _] | I]; first by left.
  by right; exact: Hd I.
move=> p1 p2 q2 [[E1 E2] | I1] [[E3 E4] | I2].
- by rewrite -E2 -E4.
- by subst p1; case: Hn; exact: Hd I2.
- by subst p1; case: Hn; exact: Hd I1.
exact: Hf I1 I2.
Qed.

(* The continuation of a let that typecheck says is a tail is a return of
   its binder, in the related instance too. *)
Lemma tail_step L k H (c1 c2 : pv -> anf pv bare)
  (cW : vinfo -> anf vinfo bare) :
  Forall (static_ok k) L -> hinv H L ->
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (c1 x1) (cW x2)) ->
  (forall x1 x2, anf_eq ((x1, x2) :: H) (c1 x1) (c2 x2)) ->
  WellFormed.is_tail cW k = true -> forall x2, c2 x2 = ARet (AVar x2).
Proof.
move=> HL [Hd _] HcW Hc Ht x2.
have Hk : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [E [H' _]] := static_in _ _ _ HL Hp; lia.
have E1 := is_tail_shape L k c1 cW HcW Hk Ht (fpv k Real).
have Hn : ~ In (fpv k Real) L.
  by apply: (fresh_notin L k _ (aids_below L k HL)).
move: (Hc (fpv k Real) x2); rewrite E1.
case: (c2 x2) => // -[q | ? | ?] //= [E | I].
  by case: E => ->.
by case: Hn; exact: Hd I.
Qed.

(* The atoms of related values have the same type. *)
Lemma atom_typed H (a1 a2 : atom pv) :
  htyped H -> atom_eq H a1 a2 ->
  of_atom (amap pw a1) = of_atom (amap pw a2) /\
  (forall l, a1 = ANat l <-> a2 = ANat l).
Proof.
move=> Ht; case: a1 a2 => [p1 | s1 | l1] [p2 | s2 | l2] //=.
- by move=> /Ht ->.
by move=> ->.
Qed.

Lemma ptype_typed H (e1 e2 : value pv bare) :
  htyped H -> value_eq H e1 e2 -> ptype e1 = ptype e2.
Proof.
move=> Ht.
case: e1 e2 => [f a | f a b | a i | a i v | c t e | lo hi bm | an lo hi i b]
  [f' a' | f' a' b' | a' i' | a' i' v' | c' t' e' | lo' hi' bm'
  | an' lo' hi' i' b'] //=.
- by move=> [<- /(atom_typed _ _ _ Ht) [-> _]].
- by move=> [<- [/(atom_typed _ _ _ Ht) [-> _] /(atom_typed _ _ _ Ht) [-> _]]].
- by move=> [/(atom_typed _ _ _ Ht) [-> _] _].
- move=> [Hl [Hh _]].
  case: lo Hl => [? | ? | l]; case: lo' => [? | ? | l'] //= El;
    case: hi Hh => [? | ? | h]; case: hi' => [? | ? | h'] //= Eh.
  by subst l' h'.
by move=> [_ [_ [/(atom_typed _ _ _ Ht) [-> _] _]]].
Qed.

(* ---------------------------------------------------------------------------
   What typecheck says of each value. *)

(* An equation between a refusal and an acceptance. *)
Ltac tc_no := let E := fresh "E" in intro E; discriminate E.

(* Splits the matches of a typecheck equation, with their equations. *)
Ltac tc_split := repeat match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "Etc" in destruct x eqn:E
  end.

Lemma is_ok_true d : is_ok d = true -> d = Ok.
Proof. by case: d. Qed.

Section Typecheck.
Variable written : option (atom vinfo).

Lemma tc_op1 p tail k f (a : atom vinfo) te :
  typecheck_value written p tail k (AOp1 f a) = (te, Ok) -> ~ is_array te.
Proof.
case: f => [| | | | | | z | s] /=;
  try (case: (ty_eqb (of_atom a) Real)); move=> E; by inversion E.
Qed.

Lemma tc_op2 p tail k f (a b : atom vinfo) te :
  typecheck_value written p tail k (AOp2 f a b) = (te, Ok) -> ~ is_array te.
Proof.
rewrite /=; case: (operation2 f) => [? |]; last by move=> E; inversion E.
rewrite /operation2_typed.
case E: (find _ _) => [[[[a0 b0] t0] s0] |]; last by move=> E'; inversion E'.
move=> E'; inversion E'; subst te.
have [Hin _] := find_some _ _ E.
case: f Hin {E E'} => /= Hin; repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ => injection H; intros; subst
  | H : False |- _ => contradiction end; by [].
Qed.

Lemma tc_get p tail k (a i : atom vinfo) te :
  typecheck_value written p tail k (AGet a i) = (te, Ok) -> ~ is_array te.
Proof. by rewrite /=; case: (_ && _) => E; inversion E. Qed.

Lemma tc_set p tail k (a i v : atom vinfo) te :
  typecheck_value written p tail k (ASet a i v) = (te, Ok) ->
  (exists iW sW, p = ArrayBody iW sW) /\ tail = true.
Proof.
rewrite /=; case: p => [| | | iW sW]; try tc_no.
case: (of_atom a) => [| | | n]; try tc_no.
case: tail => /=; last tc_no.
case: ifP => _; last tc_no.
by move=> _; split=> //; exists iW, sW.
Qed.

Lemma tc_ite p tail k c (t e : anf vinfo bare) te :
  typecheck_value written p tail k (AIte c t e) = (te, Ok) ->
  (forall iW sW, p <> ArrayBody iW sW) /\
  (exists t1, typecheck written InBranch k t = (t1, Ok)) /\
  (exists t2, typecheck written InBranch k e = (t2, Ok)) /\ te = Real.
Proof.
rewrite /=; case: p => [| | | iW sW]; try tc_no;
  (case: (ty_eqb _ _); last tc_no);
  case: (typecheck _ _ _ t) => t1 [|m1];
  case: (typecheck _ _ _ e) => t2 [|m2]; rewrite /=; try tc_no;
  (case: (_ && _); last tc_no);
  move=> E; inversion E;
  by split=> //; split; [exists t1 | split; [exists t2 |]].
Qed.

Lemma tc_map p tail k (lo hi : atom vinfo) (b : vinfo -> anf vinfo bare) te :
  typecheck_value written p tail k (AMap lo hi b) = (te, Ok) ->
  p = Top /\ tail = true /\ is_array te /\
  exists t, typecheck written ScalarBody (S k) (b (VInfo k Integer None)) =
    (t, Ok).
Proof.
rewrite /=; case: p => [| | | ? ?]; try tc_no.
case: tail; last tc_no.
case: lo => [? | ? | l]; try tc_no.
case: hi => [? | ? | h]; try tc_no.
tc_split; try tc_no; move=> E; inversion E; subst;
  (split; [by [] | split; [by [] | split; [by [] |]]]);
  eexists; (try match goal with
    H' : is_ok ?d = true |- _ => rewrite (is_ok_true _ H') end);
  reflexivity.
Qed.

Lemma tc_fold p tail k af (lo hi init : atom vinfo)
  (b : vinfo -> vinfo -> anf vinfo bare) te :
  typecheck_value written p tail k (AFold af lo hi init b) = (te, Ok) ->
  (of_atom init = Real /\ p = Top /\ ~ is_array te /\
   exists t1, typecheck written ScalarBody (S (S k))
     (b (VInfo k Integer None) (VInfo (S k) Real None)) = (t1, Ok)) \/
  (exists n, of_atom init = Array n /\ te = Array n /\
   in_place_init written p tail init = true /\
   (forall y, init = AVar y ->
      occurs_anf (vid y) (S (S k)) (b (anon k) (anon (S k))) = false) /\
   typecheck written
     (ArrayBody (AVar (VInfo k Integer None))
        (AVar (VInfo (S k) (Array n) None))) (S (S k))
     (b (VInfo k Integer None) (VInfo (S k) (Array n) None)) = (Array n, Ok)).
Proof.
rewrite /=; case: (_ && _); last tc_no.
case Er: (ty_eqb (of_atom init) Real).
  move/ty_eqb_true: Er => Er; case: p => [| | | ? ?]; try tc_no.
  case Ht: (typecheck _ ScalarBody _ _) => [t1 [|m]] /=; last tc_no.
  case: (ty_eqb t1 Real) => /=; last tc_no.
  move=> E; inversion E; subst; left.
  by split=> //; split=> //; split; [by [] | exists t1].
case Ea: (of_atom init) Er => [| | | n] //= _; try tc_no.
case Hin: (in_place_init _ _ _ _); last tc_no.
case: init Ea Hin => [y | ? | ?] /= Ea Hin; try discriminate.
case Ho: (occurs_anf (vid y) _ _) => /=.
  by case: (varg y) => [[? ?] |]; tc_no.
case Ht: (typecheck _ (ArrayBody _ _) _ _) => [t1 [|m]] /=; last tc_no.
case Et: (ty_eqb t1 (Array n)); last tc_no.
case: (reads_around_inner_loop _ _ _); first tc_no.
move=> E; inversion E; subst; right; exists n.
move/ty_eqb_true: Et Ht => -> Ht.
do 3!split=> //.
by split; [move=> y0 [<-] | ].
Qed.

(* Outside a tail, a value at the top is not an array. *)
Lemma tc_nontail k (eW : value vinfo bare) te :
  typecheck_value written Top false k eW = (te, Ok) -> ~ is_array te.
Proof.
case: eW => [f a | f a b | a i | a i v | c t e | lo hi b | af lo hi init b] Hte.
- exact: tc_op1 Hte.
- exact: tc_op2 Hte.
- exact: tc_get Hte.
- by have [[? [? ?]] _] := tc_set _ _ _ _ _ _ _ Hte.
- by have [_ [_ [_ ->]]] := tc_ite _ _ _ _ _ _ _ Hte.
- by have [_ [? _]] := tc_map _ _ _ _ _ _ _ Hte.
case: (tc_fold _ _ _ _ _ _ _ _ _ Hte) => [[_ [_ [Hn _]]] //
  | [n [_ [_ [Hin _]]]]].
by rewrite /in_place_init in Hin.
Qed.

End Typecheck.

(* ---------------------------------------------------------------------------
   The steps of an in-place loop are nbody. *)

(* The variables that a step may not return: any array other than the
   state is not read by the step, or is an argument other than the written
   one. *)
Definition hret written (L : list pv) (s1 : pv) k (bW : anf vinfo bare) :=
  forall p, In p L -> p <> s1 -> is_array (vty (pw p)) ->
  occurs_anf (vid (pw p)) k bW = false \/
  (varg (pw p) <> None /\
   forall y, written = Some y -> same_atom (AVar (pw p)) y = false).

Definition nbody_goal written (b2 : anf pv bare) : Prop :=
  forall b1 H L k bW iW s1 s2 n,
  Forall (static_ok k) L -> ids_unique L -> hinv H L ->
  anf_eq H b1 b2 -> anf_eq (gW L) b1 bW ->
  In (s1, s2) H -> In s1 L -> vty (pw s1) = Array n ->
  hret written L s1 k bW ->
  typecheck written (ArrayBody iW (AVar (pw s1))) k bW = (Array n, Ok) ->
  nbody s2 b2.

Lemma nbody_wf written : forall b2, nbody_goal written b2.
Proof.
suff [] : (forall b, nbody_goal written b) /\
  (forall e : value pv bare, match e with
     | AFold _ _ _ _ bi => forall x y, nbody_goal written (bi x y)
     | _ => True end) by [].
apply: (anf_value_ind pv bare (nbody_goal written) (fun e => match e with
     | AFold _ _ _ _ bi => forall x y, nbody_goal written (bi x y)
     | _ => True end)).
- move=> a e IHe c IHc b1 H L k bW iW s1 s2 n HL Hu Hh Hb12 Hb1W Hs Hs1 Hn
    Hr Htc.
  case: b1 Hb12 Hb1W => [a1 e1 c1 | ?] //= [He12 Hc12] Hb1W.
  case: bW Hb1W Hr Htc => [aW eW cW | ?] //= [He1W Hc1W] Hr.
  case Hte: (typecheck_value _ _ _ _ eW) => [te d].
  case: d Hte => [|m] Hte /=; last tc_no.
  move=> Htc.
  have Hcont : ~ is_array te -> forall x2, nbody s2 (c x2).
    move=> Hna x2; set x1 := fpv k te.
    have [HL' [Hu' Hh']] := fresh_ok k te L H x2 HL Hu Hh.
    have Hr' : hret written (x1 :: L) s1 (S k) (cW (VInfo k te None)).
      move=> p [<- | Hp] Hps Ha; first by case: Hna.
      case: (Hr p Hp Hps Ha) => [Ho | Hv]; last by right.
      left; move: Ho => /= /norP [_ Ho].
      rewrite (live_cont L k c1 cW x1 (VInfo k te None) _ Hc1W HL erefl
        erefl).
      exact/negbTE.
    exact: (IHc x2 (c1 x1) ((x1, x2) :: H) (x1 :: L) (S k)
      (cW (VInfo k te None)) iW s1 s2 n HL' Hu' Hh' (Hc12 x1 x2)
      (Hc1W x1 (VInfo k te None)) (or_intror Hs) (or_intror Hs1) Hn Hr' Htc).
  have Htail := tail_step L k H c1 c cW HL Hh Hc1W Hc12.
  case: e IHe He12 => [f x | f x y | x i | x i v | cc t ee | lo hi bm
    | af lo hi init bi] IHe /= He12.
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? _.
    case: eW => //= fW xW _ Hte.
    exact: Hcont (tc_op1 written (ArrayBody iW (AVar (pw s1)))
      (WellFormed.is_tail cW k) k fW xW te Hte).
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? ? _.
    case: eW => //= fW xW yW _ Hte.
    exact: Hcont (tc_op2 written (ArrayBody iW (AVar (pw s1)))
      (WellFormed.is_tail cW k) k fW xW yW te Hte).
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? _.
    case: eW => //= xW iW' _ Hte.
    exact: Hcont (tc_get written (ArrayBody iW (AVar (pw s1)))
      (WellFormed.is_tail cW k) k xW iW' te Hte).
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? ? _.
    case: eW => //= xW iW' vW _ Hte.
    have [_ Ht] := tc_set written (ArrayBody iW (AVar (pw s1)))
      (WellFormed.is_tail cW k) k xW iW' vW te Hte.
    exact: Htail.
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? ? _.
    by case: eW => //= cW' tW eW' _ Hte;
      have [Hp _] := tc_ite written (ArrayBody iW (AVar (pw s1)))
        (WellFormed.is_tail cW k) k cW' tW eW' te Hte;
      case: (Hp iW (AVar (pw s1))).
  + clear Hr; case: e1 He12 He1W Hte => //= ? ? ? _.
    by case: eW => //= loW hiW bW' _ Hte;
      have [Hp _] := tc_map written (ArrayBody iW (AVar (pw s1)))
        (WellFormed.is_tail cW k) k loW hiW bW' te Hte.
  + case: e1 He12 He1W Hte => //= af1 lo1 hi1 init1 bi1 He12.
    case: eW Hr => //= afW loW hiW initW biW Hr He1W Hte.
    case: (tc_fold written (ArrayBody iW (AVar (pw s1)))
      (WellFormed.is_tail cW k) k afW loW hiW initW biW te Hte)
      => [[_ [Hp _]] //
      | [n' [Ein [Ete [Hin [Hocc Hbt]]]]]].
    clear Hte; move: Hin => /= /andP [Htl Hsame].
    case: He1W => [_ [_ [/atom_graph [EiW Hi1L] HbW]]]; subst initW.
    case: init1 He12 Hi1L Hsame Hocc Hbt Ein Hr => [q1 | ? | ?] //=
      [_ [_ [Hq12 Hb12]]] Hi1L Hsame Hocc Hbt Ein Hr.
    have Eq1 : q1 = s1 by apply: Hu => //; [exact: Hi1L | exact/Nat.eqb_eq].
    subst q1.
    case: init Hq12 => [q2 | ? | ?] //= Hq2.
    split; first exact: (proj2 Hh _ _ _ Hq2 Hs).
    split; last exact: Htail.
    move=> x2 y2; set i1 := fpv k Integer; set s1' := fpv (S k) (Array n').
    have [HL1 [Hu1 Hh1]] := fresh_ok k Integer L H x2 HL Hu Hh.
    have [HL2 [Hu2 Hh2]] :=
      fresh_ok (S k) (Array n') (i1 :: L) ((i1, x2) :: H) y2 HL1 Hu1 Hh1.
    have Hr' : hret written (s1' :: i1 :: L) s1' (S (S k))
        (biW (VInfo k Integer None) (VInfo (S k) (Array n') None)).
      move=> p [<- | [<- | Hp]] Hps Ha //.
      case: (Nat.eq_dec (vid (pw p)) (vid (pw s1))) => [Ep | Ne].
        have Eps : p = s1 by apply: Hu.
        subst p; left.
        rewrite (live_cont2 L k bi1 biW i1 s1' (VInfo k Integer None)
          (VInfo (S k) (Array n') None) _ HbW HL erefl erefl erefl erefl).
        exact: Hocc.
      have Hps' : p <> s1 by move=> E; apply: Ne; rewrite E.
      case: (Hr p Hp Hps' Ha) => [Ho | Hv]; last by right.
      left; move: Ho => /= /norP [/norP [_ Ho] _].
      rewrite (live_cont2 L k bi1 biW i1 s1' (VInfo k Integer None)
        (VInfo (S k) (Array n') None) _ HbW HL erefl erefl erefl erefl).
      exact/negbTE.
    exact: (IHe x2 y2 (bi1 i1 s1') ((s1', y2) :: (i1, x2) :: H)
      (s1' :: i1 :: L) (S (S k))
      (biW (VInfo k Integer None) (VInfo (S k) (Array n') None))
      (AVar (VInfo k Integer None)) s1' y2 n' HL2 Hu2 Hh2 (Hb12 i1 x2 s1' y2)
      (HbW i1 (VInfo k Integer None) s1' (VInfo (S k) (Array n') None))
      (or_introl erefl) (or_introl erefl) erefl Hr' Hbt).
- move=> r b1 H L k bW iW s1 s2 n HL Hu Hh Hb12 Hb1W Hs Hs1 Hn Hr Htc.
  case: b1 Hb12 Hb1W => [? ? ? | r1] //= Hb12 Hb1W.
  case: bW Hb1W Hr Htc => [? ? ? | rW] //= Hb1W Hr Htc.
  move/atom_graph: Hb1W => [ErW Hr1L]; subst rW.
  case: r1 Hb12 Hr1L Htc Hr => [q1 | ? | ?] /= Hb12 Hr1L Htc Hr; last first.
  + by inversion Htc.
  + by inversion Htc.
  have Hq1L := Hr1L q1 erefl.
  case: r Hb12 => [q2 | ? | ?] //= Hq.
  have Ety : vty (pw q1) = Array n.
    move: Htc; case: (varg (pw q1)) => [[? ?] |]; last by move=> E; inversion E.
    by case: (_ && _) => E; inversion E.
  have Eq1 : q1 = s1.
    case: (Nat.eq_dec (vid (pw q1)) (vid (pw s1))) => [E | Ne].
      exact: Hu.
    have Hne : q1 <> s1 by move=> E; apply: Ne; rewrite E.
    have Ha : is_array (vty (pw q1)) by rewrite Ety.
    case: (Hr q1 Hq1L Hne Ha) => [Ho | [Hv Hw]].
      by rewrite /= Nat.eqb_refl in Ho.
    move: Htc; case: (varg (pw q1)) Hv => [[? ?] |] // _.
    rewrite Ety /=.
    clear Hr; case: written Hw => [y |] Hw /=; last by move=> E; inversion E.
    by have := Hw y erefl; rewrite /= => ->; move=> E; inversion E.
  subst q1; exact: (proj2 Hh _ _ _ Hq Hs).
- by [].
- by [].
- by [].
- by [].
- by [].
- by [].
by move=> af lo hi init bi IH.
Qed.

(* ---------------------------------------------------------------------------
   The bodies of branches, maps and scalar folds are nesty false. *)

Definition nfalse_goal written (b2 : anf pv bare) : Prop :=
  forall b1 H L k bW p t, p = InBranch \/ p = ScalarBody ->
  Forall (static_ok k) L -> ids_unique L -> hinv H L ->
  anf_eq H b1 b2 -> anf_eq (gW L) b1 bW ->
  typecheck written p k bW = (t, Ok) -> nesty false b2.

Definition nfalse_value written (e2 : value pv bare) : Prop :=
  forall e1 H L k eW p tail te, p = InBranch \/ p = ScalarBody ->
  Forall (static_ok k) L -> ids_unique L -> hinv H L ->
  value_eq H e1 e2 -> value_eq (gW L) e1 eW ->
  typecheck_value written p tail k eW = (te, Ok) -> nesty_value false e2.

Lemma nesty_false_wf written : forall b2, nfalse_goal written b2.
Proof.
suff [] : (forall b, nfalse_goal written b) /\
  (forall e, nfalse_value written e) by [].
apply: (anf_value_ind pv bare (nfalse_goal written) (nfalse_value written)).
- move=> a e IHe c IHc b1 H L k bW p t Hp HL Hu Hh Hb12 Hb1W Htc.
  case: b1 Hb12 Hb1W => [a1 e1 c1 | ?] //= [He12 Hc12] Hb1W.
  case: bW Hb1W Htc => [aW eW cW | ?] //= [He1W Hc1W].
  case Hte: (typecheck_value _ _ _ _ eW) => [te d].
  case: d Hte => [|m] Hte /=; last tc_no.
  move=> Htc; split.
    exact: (IHe _ _ _ _ _ _ _ _ Hp HL Hu Hh He12 He1W Hte).
  move=> x2 _; set x1 := fpv k te.
  have [HL' [Hu' Hh']] := fresh_ok k te L H x2 HL Hu Hh.
  exact: (IHc x2 (c1 x1) ((x1, x2) :: H) (x1 :: L) (S k)
    (cW (VInfo k te None)) p t Hp HL' Hu' Hh' (Hc12 x1 x2)
    (Hc1W x1 (VInfo k te None)) Htc).
- by [].
- by [].
- by [].
- by [].
- move=> x i v e1 H L k eW p tail te Hp _ _ _ He12.
  case: e1 He12 => //= x1 i1 v1 _.
  case: eW => //= xW iW vW _ Hte.
  have [[iW' [sW' Ep]] _] := tc_set written p tail k xW iW vW te Hte.
  by case: Hp; rewrite Ep.
- move=> c t IHt e IHe e1 H L k eW p tail te Hp HL Hu Hh He12.
  case: e1 He12 => //= c1 t1 f1 [_ [Ht12 Hf12]].
  case: eW => //= cW tW fW [_ [Ht1W Hf1W]] Hte.
  have [_ [[tt Htt] [[tf Htf] _]]] := tc_ite written p tail k cW tW fW te Hte.
  split.
    exact: (IHt _ _ _ _ _ _ _ (or_introl erefl) HL Hu Hh Ht12 Ht1W Htt).
  exact: (IHe _ _ _ _ _ _ _ (or_introl erefl) HL Hu Hh Hf12 Hf1W Htf).
- move=> lo hi b IHb e1 H L k eW p tail te Hp _ _ _ He12.
  case: e1 He12 => //= lo1 hi1 b1 _.
  case: eW => //= loW hiW bW _ Hte.
  have [Ep _] := tc_map written p tail k loW hiW bW te Hte.
  by case: Hp; rewrite Ep.
move=> a lo hi init b IHb e1 H L k eW p tail te Hp _ _ _ He12.
case: e1 He12 => //= a1 lo1 hi1 i1 b1 _.
case: eW => //= aW loW hiW iW bW _ Hte.
case: (tc_fold written p tail k aW loW hiW iW bW te Hte)
  => [[_ [Ep _]] | [n [_ [_ [Hin _]]]]].
  by case: Hp; rewrite Ep.
by case: Hp => Ep; rewrite Ep /in_place_init in Hin.
Qed.

(* ---------------------------------------------------------------------------
   The body of a well-formed function is nesty true. *)

Definition ntop_goal written (b2 : anf pv bare) : Prop :=
  forall b1 H L k bW t,
  Forall (static_ok k) L -> ids_unique L -> hinv H L -> htyped H ->
  (forall p, In p L -> is_array (vty (pw p)) -> varg (pw p) <> None) ->
  anf_eq H b1 b2 -> anf_eq (gW L) b1 bW ->
  typecheck written Top k bW = (t, Ok) -> nesty true b2.

Lemma nesty_top_wf written : forall b2, ntop_goal written b2.
Proof.
elim=> [a e c IH | r] b1 H L k bW t HL Hu Hh Ht Ha Hb12 Hb1W Htc //.
case: b1 Hb12 Hb1W => [a1 e1 c1 | ?] //= [He12 Hc12] Hb1W.
case: bW Hb1W Htc => [aW eW cW | ?] //= [He1W Hc1W].
case Hte: (typecheck_value _ _ _ _ eW) => [te d].
case: d Hte => [|m] Hte /=; last tc_no.
move=> Htc; split; last first.
  (* the continuation, for the binders of the type of the value *)
  move=> x2 Hx2.
  case Htl: (WellFormed.is_tail cW k) Hte => Hte.
    by rewrite (tail_step L k H c1 c cW HL Hh Hc1W Hc12 Htl x2).
  have Hna := tc_nontail written k eW te Hte.
  set x1 := fpv k te.
  have [HL' [Hu' Hh']] := fresh_ok k te L H x2 HL Hu Hh.
  have Ht' : htyped ((x1, x2) :: H).
    move=> p1 p2 [[<- <-] | I]; last exact: Ht I.
    have := ptype_ok L _ _ _ _ _ _ _ He1W Hte.
    by rewrite (ptype_typed H e1 e Ht He12) -Hx2 => -[->].
  have Ha' : forall p, In p (x1 :: L) -> is_array (vty (pw p)) ->
      varg (pw p) <> None.
    by move=> p [<- | Hp] Hpa; [case: Hna | exact: Ha].
  exact: (IH x2 (c1 x1) ((x1, x2) :: H) (x1 :: L) (S k)
    (cW (VInfo k te None)) t HL' Hu' Hh' Ht' Ha' (Hc12 x1 x2)
    (Hc1W x1 (VInfo k te None)) Htc).
(* the value *)
set tl := WellFormed.is_tail cW k in Hte.
case: e He12 => [f x | f x y | x i | x i v | cc tb eb | lo hi bm
  | af lo hi init bi] /= He12 //.
- case: e1 He12 He1W Hte => //= c1' t1 f1 [_ [Ht12 Hf12]].
  case: eW => //= cW' tW fW [_ [Ht1W Hf1W]] Hte.
  have [_ [[tt Htt] [[tf Htf] _]]] := tc_ite written Top tl k cW' tW fW te Hte.
  split.
    exact: (nesty_false_wf written _ _ _ _ _ _ _ _ (or_introl erefl) HL Hu Hh
      Ht12 Ht1W Htt).
  exact: (nesty_false_wf written _ _ _ _ _ _ _ _ (or_introl erefl) HL Hu Hh
    Hf12 Hf1W Htf).
- case: e1 He12 He1W Hte => //= lo1 hi1 bm1 [_ [_ Hb12]].
  case: eW => //= loW hiW bmW [_ [_ Hb1W]] Hte.
  have [_ [_ [_ [tb Htb]]]] := tc_map written Top tl k loW hiW bmW te Hte.
  split=> // x2; set x1 := fpv k Integer.
  have [HL' [Hu' Hh']] := fresh_ok k Integer L H x2 HL Hu Hh.
  exact: (nesty_false_wf written _ (bm1 x1) _ _ (S k) _ _ _
    (or_intror erefl) HL' Hu' Hh' (Hb12 x1 x2) (Hb1W x1 (VInfo k Integer None))
    Htb).
case: e1 He12 He1W Hte => //= af1 lo1 hi1 init1 bi1 [_ [_ [Hi12 Hb12]]].
case: eW => //= afW loW hiW initW biW [_ [_ [Hi1W HbW]]] Hte.
move/atom_graph: Hi1W => [EiW Hi1L]; subst initW.
split=> //.
case: (tc_fold written Top tl k afW loW hiW (amap pw init1) biW te Hte)
  => [[Er [_ [_ [tb Htb]]]] | [n [Ein [_ [Hin [Hocc Hbt]]]]]]; clear Hte.
  (* a scalar fold *)
  left; split.
    move=> p2 E2; subst init.
    clear Hi1L; case: init1 Hi12 Er => [p1 | ? | ?] //= Hp Er.
    by rewrite -(Ht _ _ Hp) Er.
  move=> x2 y2; set i1 := fpv k Integer; set s1 := fpv (S k) Real.
  have [HL1 [Hu1 Hh1]] := fresh_ok k Integer L H x2 HL Hu Hh.
  have [HL2 [Hu2 Hh2]] :=
    fresh_ok (S k) Real (i1 :: L) ((i1, x2) :: H) y2 HL1 Hu1 Hh1.
  exact: (nesty_false_wf written _ (bi1 i1 s1) _ _ (S (S k)) _ _ _
    (or_intror erefl) HL2 Hu2 Hh2 (Hb12 i1 x2 s1 y2)
    (HbW i1 (VInfo k Integer None) s1 (VInfo (S k) Real None)) Htb).
(* an in-place fold *)
right.
move: Hin; rewrite /in_place_init.
case: tl => //; case Ew: written => [y |] //= Hsame.
case: init1 Hi12 Hi1L Hsame Ein Hocc Hbt => [q1 | ? | ?] //= Hq Hi1L Hsame
  Ein Hocc Hbt.
have Hq1L := Hi1L q1 erefl.
case: init Hq => [q2 | ? | ?] //= Hq.
split.
  by exists q2; split=> //; rewrite -(Ht _ _ Hq) Ein.
move=> x2 y2; set i1 := fpv k Integer; set s1 := fpv (S k) (Array n).
have [HL1 [Hu1 Hh1]] := fresh_ok k Integer L H x2 HL Hu Hh.
have [HL2 [Hu2 Hh2]] :=
  fresh_ok (S k) (Array n) (i1 :: L) ((i1, x2) :: H) y2 HL1 Hu1 Hh1.
have Hr : hret written (s1 :: i1 :: L) s1 (S (S k))
    (biW (VInfo k Integer None) (VInfo (S k) (Array n) None)).
  move=> p [<- | [<- | Hp]] Hps Hpa //.
  case: (Nat.eq_dec (vid (pw p)) (vid (pw q1))) => [Ep | Ne].
    have Epq : p = q1 by apply: Hu.
    subst p; left.
    rewrite (live_cont2 L k bi1 biW i1 s1 (VInfo k Integer None)
      (VInfo (S k) (Array n) None) _ HbW HL erefl erefl erefl erefl).
    exact: Hocc.
  right; split; first exact: Ha.
  move=> y' Ey'; rewrite Ew in Ey'; case: Ey' => <-.
  case: y Ew Hsame => [w | ? | ?] //= Ew Hsame.
  move/Nat.eqb_eq: Hsame => <-.
  exact/Nat.eqb_neq.
exact: (nbody_wf written _ (bi1 i1 s1) ((s1, y2) :: (i1, x2) :: H)
  (s1 :: i1 :: L) (S (S k))
  (biW (VInfo k Integer None) (VInfo (S k) (Array n) None))
  (AVar (VInfo k Integer None)) s1 y2 n HL2 Hu2 Hh2 (Hb12 i1 x2 s1 y2)
  (HbW i1 (VInfo k Integer None) s1 (VInfo (S k) (Array n) None))
  (or_introl erefl) (or_introl erefl) erefl Hr Hbt).
Qed.

(* ---------------------------------------------------------------------------
   A well-formed function: its opened body is nesty. *)

(* The opened body, related to itself. *)
Definition diag (L : list pv) := map (fun p => (p, p)) L.

Lemma self_open (dP dP2 : adefinition pv bare) : forall L k xs L' res bP,
  adefinition_eq (diag L) dP dP2 -> open_P dP k xs L = Some (L', res, bP) ->
  exists res2 bP2, open_P dP2 k xs L = Some (L', res2, bP2) /\
    anf_eq (diag L') bP bP2.
Proof.
elim: dP dP2 => [n t r f IH | rP bP0] [n' t' r' f2 | r2 b2] L k xs L' res bP
  //=.
- move=> [? [? [? H2]]]; subst n' t' r'; case: xs => [|x xs] //= Ho.
  exact: (IH (arg_pv n t r k x) (f2 (arg_pv n t r k x))
    (arg_pv n t r k x :: L) (S k) xs L' res bP (H2 _ _) Ho).
move=> [_ H2]; case: xs => //= - [? ? ?]; subst L' res bP.
by exists r2, b2.
Qed.

Lemma diag_hinv L : hinv (diag L) L.
Proof.
split.
  by move=> p1 p2 /(in_map_iff _ _ _) [p [[<- _] Hp]].
move=> p1 p2 q2 /(in_map_iff _ _ _) [p [[E1 E2] _]].
move=> /(in_map_iff _ _ _) [q [[E3 E4] _]].
by rewrite -E2 -E4 E1 E3.
Qed.

Lemma diag_htyped L : htyped (diag L).
Proof. by move=> p1 p2 /(in_map_iff _ _ _) [p [[<- <-] _]]. Qed.

(* A well-formed result typechecks its body at the top. *)
Lemma wf_result_tc ds (r : aresult vinfo) b k :
  well_formed_result ds r b k = Ok ->
  exists w t, typecheck w Top k b = (t, Ok).
Proof.
case: r => [[| | | ?] | [v | ? | ?]] //=.
  case: (existsb _ _) => //.
  case Ht: (typecheck None Top k b) => [t [|m]] //= _.
  by exists None, t.
case: (varg v) => [[nv role] |] //.
case: (written_role role) => //.
case: (negb _) => //; case: (negb _) => //.
case Ht: (typecheck (Some (AVar v)) Top k b) => [t [|m]] //= _.
by exists (Some (AVar v)), t.
Qed.

(* The premise of adjoint_nesty_duals follows from well-formedness. *)
Theorem well_formed_nesty (f : function) (x : list (val R)) (dx : list R)
  L res bP :
  parametric f -> well_formed (normalize f) = Ok ->
  Forall2 fits (decls f) x ->
  open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] =
    Some (L, res, bP) ->
  nesty true bP.
Proof.
move=> Hpar Hwf Hfit Ho.
set xs := seed_args (decls f) x dx in Ho.
have Hnp := normalize_parametric f Hpar.
set dP := afdef (normalize f) pv in Ho.
have [new [EL [Hlen Hargs]]] := open_P_args dP 0 xs [] L res bP Ho.
rewrite app_nil_r in EL; subst new.
have [resW [bW [HrW [HbW Hwfd]]]] :=
  wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho.
have Hds : decls f = map (fun p => fst (arg_entry p)) (rev L).
  exact: (decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _
    (Hnp pv unit) Ho).
rewrite /well_formed -/(decls f) in Hwf.
case Hnrv: (non_real_varied (decls f)) Hwf => [//|] Hwf.
rewrite Hwfd Nat.add_0_l in Hwf.
have [Hargs' [_ [Hstat [Huniq _]]]] :=
  open_args_facts _ _ _ _ (length xs) Hfit Hnrv Hds Hlen erefl Hargs.
have [res2 [bP2 [Ho2 Hself]]] := self_open dP dP [] 0 xs L res bP
  (Hnp pv pv) Ho.
rewrite Ho in Ho2; case: Ho2 => _ E2; subst bP2.
have [w [t Htc]] := wf_result_tc _ _ _ _ Hwf.
apply: (nesty_top_wf w bP bP (diag L) L (length xs) bW t Hstat Huniq
  (diag_hinv L) (diag_htyped L) _ Hself HbW Htc).
by move=> p Hp _; have [i [nm [t' [r [x0 [-> _]]]]]] := Hargs' p Hp.
Qed.
