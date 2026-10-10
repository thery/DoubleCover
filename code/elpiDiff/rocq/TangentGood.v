(* TangentGood.v — theorem 1, the scoping discipline: the statements the
   tangent pass generates follow `good` (Scoping.v), which simplify relies
   on, and use no tapes. The proof follows the simulation (TangentCorrect.v,
   TangentLoops.v), without the store: every variable the code reads is in
   scope, every variable it defines is new, it assigns only writable
   variables. Unlike the simulation, it covers both branches of a test and
   the bodies of loops that run no iteration. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness SimplifyCorrect TangentCorrect TangentLoops.

From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.

(* A block that keeps the discipline when followed by any block that keeps
   it in a larger scope, opened before c', where Q holds. *)
Definition good_k (sc wr : list (dvar W)) (c' : nat) (ss : list (dstmt W))
  (Q : list (dvar W) -> list (dvar W) -> Prop) : Prop :=
  forall rest,
  (forall sc' wr', incl sc sc' -> incl wr wr' -> Forall (fun x => below c' x /\ consistent x) sc' ->
     incl wr' sc' -> Q sc' wr' -> good sc' wr' rest) ->
  good sc wr (ss ++ rest).

Lemma good_k_app sc wr c1 c2 ss1 ss2 Q1 Q2 :
  good_k sc wr c1 ss1 Q1 ->
  (forall sc1 wr1, incl sc sc1 -> incl wr wr1 -> Forall (fun x => below c1 x /\ consistent x) sc1 ->
     incl wr1 sc1 -> Q1 sc1 wr1 -> good_k sc1 wr1 c2 ss2 Q2) ->
  good_k sc wr c2 (ss1 ++ ss2) Q2.
Proof.
move=> H1 H2 rest Hr; rewrite -app_assoc; apply: H1 => sc1 wr1 I1 I2 Hb Hw HQ.
apply: (H2 sc1 wr1 I1 I2 Hb Hw HQ) => sc2 wr2 J1 J2 Hb2 Hw2 HQ2.
by apply: Hr => // x Hx; [apply: J1; apply: I1 | apply: J2; apply: I2].
Qed.

Lemma good_k_nil sc wr c (Q : list (dvar W) -> list (dvar W) -> Prop) :
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc -> Q sc wr -> good_k sc wr c [] Q.
Proof. by move=> Hb Hw HQ rest Hr; apply: Hr => //; apply: incl_refl. Qed.

(* The scope of a body: the variables opened before c, which hold the
   variables in scope the body reads and the storage it updates in place. *)
Definition scope_ok (L : list pv) (c : nat) (wP : option (atom pv)) (pp : pplace)
  (live : pv -> Prop) (sc wr : list (dvar W)) : Prop :=
  Forall (fun x => below c x /\ consistent x) sc /\ incl wr sc /\
  (forall p, In p L -> live p -> In (stored p) sc /\ (tdot (pt p) = true -> In (DotOf (stored p)) sc)) /\
  (forall o, owner wP pp = Some o -> In (stored o) wr /\ In (DotOf (stored o)) wr).

Definition good_body (bP : anf pv bare) : Prop :=
  forall L k c wP pp m bA bW bT ty sc wr,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty -> scope_ok L c wP pp (live_anf k bW) sc wr -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  let '((ss, (ve, de)), c') :=
    open_pairs (tan W (option_map (amap pt) wP) (rebuild _ bT (annotate_body_t false m k bA))) c in
  (c <= c')%nat /\
  good_k sc wr c' ss (fun sc' _ => expr_ok sc' ve /\ expr_ok sc' de).

Definition good_value (eP : value pv bare) : Prop :=
  forall L k c wP pp tail eA eW eT te n ty sc wr,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT ->
  sctx L k c wP pp (live_value k eW) ty -> scope_ok L c wP pp (live_value k eW) sc wr ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m => n = m
  | None => ~ In n sc /\ ~ In (DotOf n) sc
  end ->
  let vr := varied_value k eA in
  let '(se, c') :=
    open_pairs (tan_value W (option_map (amap pt) wP)
                  (rebuild_value _ eT (annotate_value_t false k eA)) te vr n) c in
  (c <= c')%nat /\
  good_k sc wr c' se (fun sc' _ => In n sc' /\ (vr = true -> In (DotOf n) sc')).

(* A body that returns an atom: no statement. *)
Lemma good_ret (aP : atom pv) : good_body (ARet aP).
Proof.
move=> L k c wP pp m bA bW bT ty sc wr HA HW HT Hs [Hb [Hw [Hr Ho]]] Hty Htc.
destruct bA as [| aA], bW as [| aW], bT as [| aT]; rewrite /= in HA HW HT;
  try contradiction.
case/atom_graph: HT => -> HT; case/atom_graph: HW => EW HW; subst aW.
rewrite /=; split; first lia.
apply: good_k_nil => //.
destruct aP as [p | |] => //=.
have Hl : live_anf k (ARet (amap pw (AVar p))) p.
  by rewrite /live_anf /=; apply: Nat.eqb_refl.
have [R1 R2] := Hr p (HT p erefl) Hl.
have [_ [_ [Hst [_ [_ [Hd _]]]]]] :=
  static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HT p erefl).
rewrite Hst; split; first exact: R1.
by case Et: (tdot (pt p)) => /=; auto.
Qed.

(* ---------------------------------------------------------------------------
   Expressions in scope: every variable they read is in scope. *)

Definition allv (P : dvar W -> Prop) (e : dexpr W) : Prop := forall x, In x (dvars e) -> P x.

Lemma expr_ok_allv sc e : expr_ok sc e <-> allv (fun x => In x sc) e.
Proof.
rewrite /allv.
elim: e => [x | l | z | a IHa i IHi | f a IHa | f a IHa b IHb] /=.
- by split=> [H y [<- | []] | H]; [exact: H | apply: H; left].
- by split=> // _ y [].
- by split=> // _ y [].
- rewrite IHa IHi; split=> [[H1 H2] y /(in_app_or _ _ _) [Hy | Hy] | H]; auto.
  by split=> y Hy; apply: H; apply: in_or_app; auto.
- exact: IHa.
rewrite IHa IHb; split=> [[H1 H2] y /(in_app_or _ _ _) [Hy | Hy] | H]; auto.
by split=> y Hy; apply: H; apply: in_or_app; auto.
Qed.

Lemma expr_ok_incl sc sc' e : incl sc sc' -> expr_ok sc e -> expr_ok sc' e.
Proof. by move=> I; rewrite !expr_ok_allv => H x Hx; apply/I/H. Qed.

Lemma allv_op1 P f e : allv P e -> allv P (DOp1 f e).
Proof. by []. Qed.
Lemma allv_op2 P f e1 e2 : allv P e1 -> allv P e2 -> allv P (DOp2 f e1 e2).
Proof. by move=> H1 H2 x /= /(in_app_or _ _ _) [Hx | Hx]; auto. Qed.
Lemma allv_at P e1 e2 : allv P e1 -> allv P e2 -> allv P (DAt e1 e2).
Proof. by move=> H1 H2 x /= /(in_app_or _ _ _) [Hx | Hx]; auto. Qed.
Lemma allv_lit P l : allv P (DReal l).
Proof. by move=> x []. Qed.
Lemma allv_int P z : allv P (DInt z).
Proof. by move=> x []. Qed.
Lemma allv_scale P p e : allv P p -> allv P e -> allv P (scale p e).
Proof.
move=> H1 H2; case: p H1 => [x | s | z | a i | f a | f a b] H1;
  try by apply: allv_op2.
rewrite /scale; case: (String.eqb s "1") => //.
by case: (String.eqb s "-1"); [apply: allv_op1 | apply: allv_op2].
Qed.
Lemma allv_sum P l : Forall (allv P) l -> allv P (sum l).
Proof.
elim=> [| e l' He Hl IH] /=; first exact: allv_lit.
by case: l' Hl IH => [| e' l'] Hl IH //; apply: allv_op2.
Qed.

Lemma allv_partial1 P f (a : atom (tvar W)) p :
  allv P (spell a) -> allv P (dot a) -> partial1 f a = Some p -> allv P (scale (spell_partial p) (dot a)).
Proof.
move=> Hs Hd Hp; apply: allv_scale; last exact: Hd.
destruct f as [| | | | | | z |]; rewrite /= in Hp; try discriminate;
  try (destruct z); case: Hp => <- /=;
  repeat (apply allv_op1 || apply allv_op2 || apply allv_lit || assumption).
Qed.

Lemma allv_partial2 P f (a b : atom (tvar W)) pa pb :
  allv P (spell a) -> allv P (dot a) -> allv P (spell b) -> allv P (dot b) ->
  partial2 f a b = Some (pa, pb) -> allv P (sum (tangent_term W a pa ++ tangent_term W b pb)).
Proof.
move=> Hsa Hda Hsb Hdb Hp; apply: allv_sum; rewrite /tangent_term.
destruct f; rewrite /= in Hp; try discriminate; case: Hp => <- <-;
  case: (tvaried_atom a); case: (tvaried_atom b) => /=;
  repeat (apply Forall_cons || apply Forall_nil || apply allv_scale
          || apply allv_op1 || apply allv_op2 || apply allv_lit
          || assumption).
Qed.

(* An atom of a value, in scope. *)
Lemma atom_in_scope k sc (aP : atom pv) :
  (forall p, aP = AVar p -> static_ok k p /\ In (stored p) sc /\ (tdot (pt p) = true -> In (DotOf (stored p)) sc)) ->
  allv (fun x => In x sc) (spell (amap pt aP)) /\ allv (fun x => In x sc) (dot (amap pt aP)).
Proof.
case: aP => [p | |] H /=; try by split=> x [].
have [[_ [_ [Hst _]]] [H1 H2]] := H p erefl; rewrite Hst; split.
  by move=> x [<- | []].
by case Et: (tdot (pt p)) => /=; [move=> x [<- | []]; auto | move=> x []].
Qed.

(* ---------------------------------------------------------------------------
   The operations: definitions of new constants. *)

Lemma good_constants j c sc wr (t : ty) e1 e2 (Q : list (dvar W) -> list (dvar W) -> Prop) :
  expr_ok sc e1 -> expr_ok sc e2 -> ~ In (DBound (j, j)) sc -> ~ In (DotOf (DBound (j, j))) sc -> (j < c)%nat ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  Q (DotOf (DBound (j, j)) :: DBound (j, j) :: sc) wr ->
  good_k sc wr c [DDefine (DConstant t) (DBound (j, j)) e1; DDefine (DConstant Real) (DotOf (DBound (j, j))) e2] Q.
Proof.
move=> H1 H2 N1 N2 Hj Hb Hw HQ rest Hr /=.
apply: GoodConstant; [exact: H1 | exact: N1 | by [] |].
apply: GoodConstant; [ | by case | by [] |].
  by apply: (expr_ok_incl sc _ _ _ H2) => x Hx; right.
apply: Hr; [by move=> x Hx; right; right | exact: incl_refl | |
            by move=> x Hx; right; right; apply: Hw | exact: HQ].
by constructor; [split=> /=; [lia | by []] |
                 constructor; [split=> /=; [lia | by []] | exact: Hb]].
Qed.

Lemma good_constant j c sc wr (t : ty) e1 (Q : list (dvar W) -> list (dvar W) -> Prop) :
  expr_ok sc e1 -> ~ In (DBound (j, j)) sc -> (j < c)%nat ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  Q (DBound (j, j) :: sc) wr ->
  good_k sc wr c [DDefine (DConstant t) (DBound (j, j)) e1] Q.
Proof.
move=> H1 N1 Hj Hb Hw HQ rest Hr /=.
apply: GoodConstant; [exact: H1 | exact: N1 | by [] |].
apply: Hr; [by move=> x Hx; right | exact: incl_refl | |
            by move=> x Hx; right; apply: Hw | exact: HQ].
by constructor; [split=> /=; [lia | by []] | exact: Hb].
Qed.

Ltac gvalue_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in
  intros L k c wP pp tail eA eW eT te n ty sc wr HA HW HT Hs [Hb [Hw [Hr Ho]]] Htc Htail [j [Ej Hj]] Hst;
  destruct eA, eW, eT; simpl in HA, HW, HT; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.

(* The facts on an atom of the value: in scope. *)
Lemma operand_scope L k c wP pp (live : pv -> Prop) ty sc (aP : atom pv) :
  sctx L k c wP pp live ty ->
  (forall p, In p L -> live p -> In (stored p) sc /\ (tdot (pt p) = true -> In (DotOf (stored p)) sc)) ->
  (forall p, aP = AVar p -> In p L /\ live p) ->
  allv (fun x => In x sc) (spell (amap pt aP)) /\ allv (fun x => In x sc) (dot (amap pt aP)).
Proof.
move=> Hs Hr Ha; apply: (atom_in_scope k) => p E; have [Hp Lp] := Ha p E.
split; first exact: (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp).
exact: Hr p Hp Lp.
Qed.

Lemma good_op1 f (aP : atom pv) : good_value (AOp1 f aP).
Proof.
gvalue_intro.
rewrite /= in Htc Hst *; rename f2 into g.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AOp1 g (amap pw aP)) p.
  by move=> p E; split; [auto | subst; rewrite /live_value /= Nat.eqb_refl].
have [A1 A2] := operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv.
case: Hst => N1 N2.
case: (varied (amap pa aP)) => /=; (split; [lia |]).
  apply: good_constants => //.
  - by apply/expr_ok_allv; apply: allv_op1.
  - apply/expr_ok_allv.
    case Hp: (partial1 g (amap pt aP)) => [p |]; last exact: allv_lit.
    rewrite /tangent_term.
    case: (tvaried_atom (amap pt aP)); last exact: allv_lit.
    apply: allv_sum; constructor; last by constructor.
    by apply: (allv_partial1 _ g _ p).
  by split; [right; left | move=> _; left].
apply: good_constant => //.
  by apply/expr_ok_allv; apply: allv_op1.
by split; [left |].
Qed.

Lemma good_op2 f (aP bP : atom pv) : good_value (AOp2 f aP bP).
Proof.
gvalue_intro.
rewrite /= in Htc Hst *; rename f2 into g.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AOp2 g (amap pw aP) (amap pw bP)) p.
  by move=> p E; split; [auto | subst; rewrite /live_value /= Nat.eqb_refl].
have Hlv' : forall p, bP = AVar p ->
    In p L /\ live_value k (AOp2 g (amap pw aP) (amap pw bP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl orb_true_r.
have [A1 A2] := operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv.
have [B1 B2] := operand_scope _ _ _ _ _ _ _ _ bP Hs Hr Hlv'.
case: Hst => N1 N2.
case: (if comparison g then false
       else varied (amap pa aP) || varied (amap pa bP))
  => /=; (split; [lia |]).
  apply: good_constants => //.
  - by apply/expr_ok_allv; apply: allv_op2.
  - apply/expr_ok_allv.
    case Hp: (partial2 g (amap pt aP) (amap pt bP)) => [[qa qb] |]; last first.
      exact: allv_lit.
    by apply: (allv_partial2 _ g _ _ qa qb).
  by split; [right; left | move=> _; left].
apply: good_constant => //.
  by apply/expr_ok_allv; apply: allv_op2.
by split; [left |].
Qed.

Lemma good_get (aP iP : atom pv) : good_value (AGet aP iP).
Proof.
gvalue_intro.
rewrite /= in Htc Hst *.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p.
  by move=> p E; split; [auto | subst; rewrite /live_value /= Nat.eqb_refl].
have Hlv' : forall p, iP = AVar p ->
    In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl orb_true_r.
have [A1 A2] := operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv.
have [B1 B2] := operand_scope _ _ _ _ _ _ _ _ iP Hs Hr Hlv'.
case: Hst => N1 N2.
rewrite (tvaried_amap k aP).
  move=> p E; apply: (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs)).
  by case: (Hlv p E).
case: (varied (amap pa aP)) => /=; (split; [lia |]).
  apply: good_constants => //.
  - by apply/expr_ok_allv; apply: allv_at.
  - by apply/expr_ok_allv; apply: allv_at.
  by split; [right; left | move=> _; left].
apply: good_constant => //.
  by apply/expr_ok_allv; apply: allv_at.
by split; [left |].
Qed.

Lemma good_set (aP iP vP : atom pv) : good_value (ASet aP iP vP).
Proof.
gvalue_intro.
rewrite /= in Htc *.
destruct pp as [| | | ix sx]; rewrite /= in Htc; try discriminate.
move: Htc; case Eat: (of_atom (amap pw aP)) => [| | | z] // Htc.
destruct tail; rewrite /= in Htc; last discriminate.
destruct aP as [a | |]; rewrite /= in Htc Eat; try discriminate.
move: Htc; case Ea: (vid (pw a) =? vid (pw sx))%nat => //= Htc.
have [Hix [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
have Ha : In a L by auto.
have Eas := same_vid_s _ _ _ _ _ _ _ _ _ Hs Ha Hsx Ea; subst a.
rewrite /= in Hst; case: Hst => Ej _; subst j.
have [W1 W2] := Ho sx erefl.
have Hlv : forall p, iP = AVar p \/ vP = AVar p ->
    In p L /\
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p.
  by move=> p [E | E]; subst; split; auto;
    rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
have [I1 I2] :=
  operand_scope _ _ _ _ _ _ _ _ iP Hs Hr (fun p E => Hlv p (or_introl E)).
have [V1 V2] :=
  operand_scope _ _ _ _ _ _ _ _ vP Hs Hr (fun p E => Hlv p (or_intror E)).
case: (varied (amap pa (AVar sx)) || varied (amap pa vP)) => /=;
  (split; [lia |]); move=> rest Hrest /=.
  apply: GoodAssign; [split; [exact: W1 | apply/expr_ok_allv; exact: I1] |
                      apply/expr_ok_allv; exact: V1 |].
  apply: GoodAssign; [split; [exact: W2 | apply/expr_ok_allv; exact: I1] |
                      apply/expr_ok_allv; exact: V2 |].
  apply: (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw).
  by split; [apply: Hw; exact: W1 | move=> _; apply: Hw; exact: W2].
apply: GoodAssign; [split; [exact: W1 | apply/expr_ok_allv; exact: I1] |
                    apply/expr_ok_allv; exact: V1 |].
apply: (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw).
by split; [apply: Hw; exact: W1 |].
Qed.

(* ---------------------------------------------------------------------------
   A let. *)

Lemma sctx_weaken L k c c' wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  sctx L k c' wP pp live' ty.
Proof.
move=> Hc Hl Hcc; case: Hc => HS HU HN HW HP HO HA HT HTop; constructor; auto.
- by move=> p Hp; have := HN p Hp; lia.
- move=> o p Ho Hp E.
  by case: (HO o p Ho Hp E) => [H | H]; [left | right; auto].
by move=> y H1 H2 H3; case: (HTop y H1 H2 H3); auto.
Qed.

Lemma scope_weaken L c c' wP pp (live live' : pv -> Prop) sc wr :
  scope_ok L c wP pp live sc wr -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  scope_ok L c' wP pp live' sc wr.
Proof.
move=> [Hb [Hw [Hr Ho]]] Hl Hc; split.
  apply: (Forall_impl _ _ Hb) => x [H1 H2]; split=> //.
  exact: (below_mono _ _ _ H1 Hc).
by split=> //; split=> // p Hp Lp; apply: Hr; auto.
Qed.

(* A value of an array type, or a real, with zero tangents. *)
Definition default_dual (t : ty) : val (dual R) :=
  match t with
  | Real => VReal (Dual 0 0)
  | Integer => VInt 0
  | Boolean => VBool false
  | Array n => VArray (repeat (Dual 0 0) (Z.to_nat n))
  end.

Lemma default_dual_ok t : has_type t (default_dual t) /\ zero (default_dual t).
Proof.
case: t => [| | | n] /=; split; auto; first exact: repeat_length.
by apply/Forall_forall => x Hx; rewrite (repeat_spec _ _ _ Hx).
Qed.

(* A varied value is a real or an array. *)
Lemma varied_real_or_array L k wW pW tail (eP : value pv bare) eA eW te :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L ->
  typecheck_value wW pW tail k eW = (te, Ok) -> varied_value k eA = true -> real_or_array te.
Proof.
move=> HA HW HL Htc Hv.
destruct eP, eA, eW; rewrite /= in HA HW; try contradiction;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : atom_eq (gA L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  end; subst; rewrite /= in Htc Hv.
- by destruct f1; rewrite /= in Htc; crush_match Htc; case: Htc => <-.
- destruct (comparison f1) eqn:Hcmp; first discriminate.
  crush_match Htc; case: Htc => <-.
  have Hra : forall aP : atom pv, (forall p, aP = AVar p -> In p L) ->
      varied (amap pa aP) = true -> real_or_array (of_atom (amap pw aP)).
    move=> aP Ha Hva; case: aP Ha Hva => [q | |] Ha //= Hva.
    have [E1 [_ [_ [_ [_ [_ [_ [H' _]]]]]]]] := static_in _ _ _ HL (Ha q erefl).
    exact: H' Hva.
  case/orb_true_iff: Hv => Hv;
    [have Hr' := Hra a H0 Hv | have Hr' := Hra b H1 Hv];
    destruct f1; rewrite /= in Hcmp; try discriminate;
    rewrite /operation2_typed in Heqo0;
    destruct (of_atom (amap pw a)), (of_atom (amap pw b)); simpl in *;
    try contradiction; try discriminate; by case: Heqo0 => <-.
- by crush_match Htc; case: Htc => <-.
- by destruct pW; rewrite /= in Htc; crush_match Htc; case: Htc => <-.
- by destruct pW; rewrite /= in Htc; crush_match Htc; case: Htc => <-.
- destruct pW; rewrite /= in Htc; try (crush_match Htc; fail).
  destruct tail; last crush_match Htc.
  by destruct lo, hi; rewrite /= in Htc; crush_match Htc; case: Htc => <-.
by crush_match Htc; case: Htc => <-.
Qed.

Lemma good_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  good_value eP -> (forall x, good_body (cP x)) -> good_body (ALet a eP cP).
Proof.
move=> IHe IHb L k c wP pp m bA bW bT ty sc wr HA HW HT Hs Hsc Hty Htc.
destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |];
  rewrite /= in HA HW HT; try contradiction.
case: HA => HeA HcA; case: HW => HeW HcW; case: HT => HeT HcT.
rewrite /= in Htc; move: Htc.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
             (WellFormed.is_tail cW k) k eW) => [te d0].
case: d0 Hte => [| msg] Hte /= Htc //.
cbn [annotate_body_t].
case: (needs false m (S k) (cA (let_binder k eA))) => u l.
set vr := varied_value k eA; set vt := annotate_value_t false k eA.
set rest := annotate_body_t false m (S k) (cA (let_binder k eA)).
cbn [rebuild]; rewrite tan_let; cbv zeta.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
have Hwr : forall a0, wP = Some a0 -> exists y, a0 = AVar y /\ In y L.
  move=> a0 E; have [y [-> [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ E.
  by exists y.
have [n [rec [c0 [Hopen Hn]]]] :=
  open_with_storage L k wP eP eT vt (fun v0 => rebuild _ (cT v0) rest)
    (fun n rec => sbind (tan_value W (option_map (amap pt) wP)
                           (rebuild_value _ eT vt) te vr n)
       (fun se => sbind (tan W (option_map (amap pt) wP)
                           (rebuild _ (cT (open_let te n vr rec)) rest))
                    (fun '(sb, vd) => Done ((se ++ sb)%list, vd))))
    c HeT HL Hwr.
rewrite Hopen.
have Htid : forall p, In p L ->
    (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat.
  by move=> p Hp; have [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]] := static_in _ _ _ HL Hp.
rewrite -(is_tail_transfer L k cP cW cT rest HcW HcT Htid) in Hn.
set tail := WellFormed.is_tail cW k in Hte Hn *.
rewrite open_pairs_sbind.
case Hse: (open_pairs (tan_value W _ (rebuild_value (tvar W) eT vt) te vr n) c0)
  => [se c1].
have Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by move=> p H; rewrite /live_value /live_anf /= in H *; rewrite H.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Hnum : exists j, n = DBound (j, j) /\ (j < c0)%nat /\ (c <= c0)%nat /\
    match storage wP tail eP return Prop with
    | Some _ => True | None => j = c end.
  case Es: (storage wP tail eP) Hn => [m0 |] [-> ->]; last first.
    by exists c; repeat split; lia.
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [_ [o [Ho Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em; subst m0.
  exists (pn o); split=> //.
  have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho); lia.
have [j [Ej [Hj0 [Hc0 Hjs]]]] := Hnum.
case: Hsc => Hb [Hw [Hr Ho]].
have Hst : match storage wP tail eP return Prop with
           | Some m0 => n = m0
           | None => ~ In n sc /\ ~ In (DotOf n) sc
           end.
  case: (storage wP tail eP) Hn Hjs => [m0 | ] Hn Hjs; first by case: Hn.
  subst j; rewrite Ej.
  by split=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _];
    rewrite /= in Hbl; lia.
have IH0 := IHe L k c0 wP pp tail eA eW eT te n ty sc wr HeA HeW HeT
          (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hc0)
          (scope_weaken _ _ _ _ _ _ _ _ _ (conj Hb (conj Hw (conj Hr Ho)))
             Hlive_e Hc0)
          Hte Htail_ty (ex_intro _ j (conj Ej Hj0)) Hst.
cbv zeta in IH0; rewrite -/vr -/vt Hse in IH0.
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
  rewrite Es in Es'; case: Es' => Em0; subst m0.
  have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
  have ET : cT (pt x) = ARet (AVar (pt x)).
    move: (HcT x (pt x)); rewrite Hcx.
    case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gT: I => I _.
  rewrite /= in ET; rewrite ET /=.
  split; first lia.
  rewrite app_nil_r => rest' Hrest.
  apply: Hgk1 => sc1 wr1 I1 I2 Hb1 Hw1 [Q1 Q2]; apply: Hrest; auto.
  by split=> //=; case: (vr) Q2 => //= Q2; apply: Q2.
(* a fresh variable *)
case: Hn => En Hc0'; subst n j.
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
have Hsc' : forall sc1 wr1, incl sc sc1 -> incl wr wr1 ->
    Forall (fun x0 => below c1 x0 /\ consistent x0) sc1 -> incl wr1 sc1 ->
    In (DBound (c, c)) sc1 -> (vr = true -> In (DotOf (DBound (c, c))) sc1) ->
    scope_ok (x :: L) c1 wP pp (live_anf (S k) cW') sc1 wr1.
  move=> sc1 wr1 I1 I2 Hb1 Hw1 Q1 Q2; split=> //; split=> //; split.
    move=> p [<- | Hp] Hl; first by split; [exact: Q1 | exact: Q2].
    have [R1 R2] := Hr p Hp (Hlive_c p Hp Hl).
    by split; [apply: I1 | move=> Hd; apply: I1; apply: R2].
  by move=> o Ho'; have [W1 W2] := Ho o Ho'; split; apply: I2.
have {}IHb := IHb x.
case Hsb: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) (cT (open_let te (DBound (c, c)) vr rec)) rest))
             c1) => [[sb [ve' de']] c2] /=.
have Hsc0 : scope_ok (x :: L) c1 wP pp (live_anf (S k) cW')
              (DBound (c, c) :: DotOf (DBound (c, c)) :: sc) wr.
  apply: Hsc'; [by move=> y Hy; right; right | exact: incl_refl | |
                by move=> y Hy; right; right; apply: Hw | by left |
                by move=> _; right; left].
  constructor; first by split=> /=; [lia | by []].
  constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [H1 H2]; split=> //.
  by apply: (below_mono c); [exact: H1 | lia].
have IH0 := IHb (x :: L) (S k) c1 wP pp m (cA (pa x)) cW' (cT (pt x)) ty _ _
              (HcA x _) (HcW x _) (HcT x _) Hs' Hsc0 Hty Htc.
rewrite /x in IH0; cbn [pt pa] in IH0; rewrite -/rest Hsb in IH0.
case: IH0 => Hc12 _.
split; first lia.
apply: (good_k_app sc wr c1 c2 se sb _ _ Hgk1) => sc1 wr1 I1 I2 Hb1 Hw1 [Q1 Q2].
have IH1 := IHb (x :: L) (S k) c1 wP pp m (cA (pa x)) cW' (cT (pt x)) ty sc1 wr1
              (HcA x _) (HcW x _) (HcT x _) Hs'
              (Hsc' sc1 wr1 I1 I2 Hb1 Hw1 Q1 Q2) Hty Htc.
rewrite /x in IH1; cbn [pt pa] in IH1; rewrite -/rest Hsb in IH1.
exact: (proj2 IH1).
Qed.

(* ---------------------------------------------------------------------------
   A branch. *)

Lemma sctx_sub L k c wP pp pp' (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> owner wP pp' = None -> pp' <> PTop -> place_ok L pp' ->
  sctx L k c wP pp' live' Real.
Proof.
by move=> Hc Ho Hpp Hpl; case: Hc => *; constructor; auto; move=> *; congruence.
Qed.

Lemma good_assign_end sc wr (n : dvar W) e1 e2 (vr : bool) :
  In n wr -> In (DotOf n) wr \/ vr = false -> expr_ok sc e1 -> expr_ok sc e2 ->
  good sc wr (if vr then [DAssign (DVar n) e1; DAssign (DVar (DotOf n)) e2] else [DAssign (DVar n) e1]).
Proof.
move=> H1 H2 E1 E2; case: vr H2 => H2.
  apply: GoodAssign; [exact: H1 | exact: E1 |].
  by apply: GoodAssign; [case: H2 | exact: E2 | constructor].
by apply: GoodAssign; [exact: H1 | exact: E1 | constructor].
Qed.

Lemma good_ite (cP : atom pv) (tP eP : anf pv bare) :
  good_body tP -> good_body eP -> good_value (AIte cP tP eP).
Proof.
move=> IHt IHe.
gvalue_intro.
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
case: Hst => N1 N2.
have Hlc : forall p, cP = AVar p ->
    In p L /\ live_value k (AIte (amap pw cP) tW eW) p.
  by move=> p E; split; [auto | subst; rewrite /live_value /= Nat.eqb_refl].
have [C1 _] := operand_scope _ _ _ _ _ _ _ _ cP Hs Hr Hlc.
(* the two bodies, opened *)
rewrite open_pairs_sbind.
case Hot: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) tT (annotate_body_t false Replay k tA))) c)
  => [[st [vt dt]] c1].
rewrite open_pairs_sbind.
case Hoe: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) eT (annotate_body_t false Replay k eA))) c1)
  => [[se' [ve' de']] c2].
cbn zeta; rewrite /=.
set vr := varied_anf k tA || varied_anf k eA.
set n := DBound (j, j).
set sc2 := if vr then DotOf n :: n :: sc else n :: sc.
set wr2 := if vr then DotOf n :: n :: wr else n :: wr.
have Hsc2 : incl sc sc2 by rewrite /sc2; case: (vr) => y Hy /=; auto.
have Hwr2 : incl wr2 sc2.
  by rewrite /sc2 /wr2; case: (vr) => y /= Hy; intuition.
have Hn2 : In n wr2 /\ (In (DotOf n) wr2 \/ vr = false).
  by rewrite /wr2; case: (vr) => /=; auto.
have Hb2 : forall c', (c <= c')%nat ->
    Forall (fun x => below c' x /\ consistent x) sc2.
  move=> c' Hc'; rewrite /sc2.
  have Hsc : Forall (fun x => below c' x /\ consistent x) sc.
    apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
    exact: (below_mono _ _ _ Y1 Hc').
  by case: (vr); repeat constructor; auto; rewrite /=; lia.
(* a branch body *)
have Hbr : forall bP bA bW bT (cb cb' : nat) sb vb db,
    anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
    good_body bP -> (c <= cb)%nat ->
    (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
    typecheck (option_map (amap pw) wP) InBranch k bW = (Real, Ok) ->
    open_pairs (tan W (option_map (amap pt) wP)
                  (rebuild (tvar W) bT (annotate_body_t false Replay k bA))) cb
      = ((sb, (vb, db)), cb') ->
    (cb <= cb')%nat /\
    good sc2 wr2 (sb ++ (if vr then [DAssign (DVar n) vb;
                                     DAssign (DVar (DotOf n)) db]
                         else [DAssign (DVar n) vb]))%list.
  move=> bP bA bW bT cb cb' sb vb db HA HW HT IH Hcb Hl Htb Hob.
  have Hs' : sctx L k cb wP PBranch (live_anf k bW) Real.
    apply: (sctx_sub L k cb wP pp PBranch
              (live_value k (AIte (amap pw cP) tW eW)) _ ty) => //.
    by apply: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs); auto.
  have Hsc' : scope_ok L cb wP PBranch (live_anf k bW) sc2 wr2.
    split; first exact: (Hb2 _ Hcb).
    split; first exact: Hwr2.
    split; last by move=> o E.
    move=> p Hp Lp; have [R1 R2] := Hr p Hp (Hl p Lp).
    by split; [apply: Hsc2 | move=> Hd; apply: Hsc2; apply: R2].
  have := IH L k cb wP PBranch Replay bA bW bT Real sc2 wr2 HA HW HT Hs' Hsc'
            I Htb.
  rewrite Hob => -[Hc' Hg].
  split; first exact: Hc'.
  apply: Hg => sc' wr' I1 I2 _ _ [Q1 Q2].
  apply: good_assign_end;
    [apply: I2; exact: (proj1 Hn2) | | exact: Q1 | exact: Q2].
  by case: (proj2 Hn2) => [Hq | Hq]; [left; apply: I2 | right].
have Hlt : forall p, live_anf k tW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' orb_true_r.
have Hle : forall p, live_anf k eW p ->
    live_value k (AIte (amap pw cP) tW eW) p.
  by rewrite /live_anf /live_value => p H' /=; rewrite H' !orb_true_r.
have [Hc1 Hg1] :=
  Hbr tP tA tW tT c c1 st vt dt HAt HWt HTt IHt (le_n c) Hlt HtW Hot.
have [Hc2 Hg2] :=
  Hbr eP eA eW eT c1 c2 se' ve' de' HAe HWe HTe IHe Hc1 Hle HeW Hoe.
split; first lia.
move=> rest Hrest; destruct vr eqn:Hvr; rewrite /=.
  apply: GoodRealVar; [exact: N1 | by [] |].
  apply: GoodRealVar; [by case | by [] |].
  have Hc : expr_ok sc2 (spell (amap pt cP)).
    by apply: (expr_ok_incl sc) Hsc2 _; apply/expr_ok_allv.
  apply: GoodBranch; [exact: Hc | exact: Hg1 | exact: Hg2 |].
  apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
                 exact: Hwr2 |].
  by split=> /=; auto.
apply: GoodRealVar; [exact: N1 | by [] |].
have Hc : expr_ok sc2 (spell (amap pt cP)).
  by apply: (expr_ok_incl sc) Hsc2 _; apply/expr_ok_allv.
apply: GoodBranch; [exact: Hc | exact: Hg1 | exact: Hg2 |].
apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
               exact: Hwr2 |].
by split=> /=; auto.
Qed.

(* ---------------------------------------------------------------------------
   Loops. *)

Lemma sctx_scalar (L : list pv) k c wP (live : pv -> Prop) :
  Forall (static_ok k) L -> ids_unique L -> (forall p, In p L -> (pn p < c)%nat) ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L /\ varg (pw y) <> None) ->
  sctx L k c wP PScalar live Real.
Proof. by move=> *; constructor. Qed.

Lemma good_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, good_body (bP x)) -> good_value (AMap loP hiP bP).
Proof.
move=> IHb.
gvalue_intro.
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
rewrite /= in Hst; case: Hst => Ej _; subst j.
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
have [W1 W2] := Ho o Hown.
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
cbn [open_pairs spell amap].
set vr := varied_anf (S k) (bA (fresh k)).
set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
            (VInt 0) c.
have Hix : static_ok (S k) ix.
  by repeat split; rewrite /=; auto; try lia; discriminate.
have Hs' : sctx (ix :: L) (S k) (S c) (Some (AVar o)) PScalar
             (live_anf (S k) (bW (VInfo k Integer None))) Real.
  apply: sctx_scalar.
  - constructor=> //; apply: (Forall_impl _ _ HL) => p Hp.
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
have Hsc' : scope_ok (ix :: L) (S c) (Some (AVar o)) PScalar
              (live_anf (S k) (bW (VInfo k Integer None)))
              (DBound (c, c) :: sc) wr.
  split; first exact: Hcons.
  split; first by move=> y Hy; right; apply: Hw.
  split; last by move=> o' E.
  move=> p [<- | Hp] Lp; first by split; [left |].
  have [R1 R2] := Hr p Hp (Hlive_b p Hp Lp).
  by split; [right | move=> Hd; right; apply: R2].
have := IHb ix (ix :: L) (S k) (S c) (Some (AVar o)) PScalar Replay
          (bA (fresh k)) (bW (VInfo k Integer None))
          (bT (open_index (DBound (c, c)))) Real (DBound (c, c) :: sc) wr
          (HbA ix _) (HbW ix _) (HbT ix _) Hs' Hsc' I HtB.
rewrite Hob => -[Hc2 Hg].
split; first lia.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
have Hb2 : Forall (fun x => below c2 x /\ consistent x) sc.
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
move=> rest Hrest; rewrite /tan_map; destruct vr eqn:Hvr; rewrite /=;
  (apply: GoodFor; [exact: Hni | by [] | exact I | exact I | |]).
- apply: Hg => sc' wr' I1 I2 _ _ [Q1 Q2].
  apply: GoodAssign;
    [split; [apply: I2; exact: W1 | by apply: I1; left] | exact: Q1 |].
  by apply: GoodAssign;
    [split; [apply: I2; exact: W2 | by apply: I1; left] | exact: Q2 |
     constructor].
- apply: Hrest; [exact: incl_refl | exact: incl_refl | exact: Hb2 |
                 exact: Hw |].
  by split; [apply: Hw; exact: W1 | move=> _; apply: Hw; exact: W2].
- apply: Hg => sc' wr' I1 I2 _ _ [Q1 Q2].
  apply: GoodAssign;
    [split; [apply: I2; exact: W1 | by apply: I1; left] | exact: Q1 |].
  by apply: GoodAssign;
    [split; [apply: I2; exact: W2 | by apply: I1; left] | exact I |
     constructor].
apply: Hrest; [exact: incl_refl | exact: incl_refl | exact: Hb2 | exact: Hw |].
by split; [apply: Hw; exact: W1 |].
Qed.

Lemma good_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall x y, good_body (bP x y)) -> good_value (AFold a loP hiP initP bP).
Proof.
move=> IHb.
gvalue_intro.
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
have [L1 _] :=
  operand_scope _ _ _ _ _ _ _ _ loP Hs Hr (fun p E => Hlv p (or_introl E)).
have [H1' _] := operand_scope _ _ _ _ _ _ _ _ hiP Hs Hr
                  (fun p E => Hlv p (or_intror (or_introl E))).
have [I1 I2] := operand_scope _ _ _ _ _ _ _ _ initP Hs Hr
                  (fun p E => Hlv p (or_intror (or_intror E))).
set svr := fold_varied k (amap pa initP) bA.
have Hni : ~ In (DBound (c, c)) sc.
  move=> I; move/Forall_forall: Hb => /(_ _ I) [Hbl _].
  by rewrite /= in Hbl; lia.
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
  case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
  cbn [open_pairs].
  change (varied (amap pa initP) ||
          varied_anf (S (S k)) (bA (fresh k) (fresh (S k)))) with svr.
  set n := DBound (j, j) in N1 N2 Hob *.
  set ix := PV (AV k false) (VInfo k Integer None)
              (TVar (DBound (c, c)) Integer None false false false false None)
              (VInt 0) c.
  set sx := PV (AV (S k) svr) (VInfo (S k) Real None)
              (TVar n Real None svr svr svr false None) (VReal (Dual 0 0)) j.
  set sc2 := if svr then DotOf n :: n :: sc else n :: sc.
  set wr2 := if svr then DotOf n :: n :: wr else n :: wr.
  have Hsc2 : incl sc sc2 by rewrite /sc2; case: (svr) => y Hy /=; auto.
  have Hwr2 : incl wr2 sc2.
    by rewrite /sc2 /wr2; case: (svr) => y /= Hy; intuition.
  have Hb2 : forall c', (c <= c')%nat ->
      Forall (fun x => below c' x /\ consistent x) sc2.
    move=> c' Hc'; rewrite /sc2.
    have Hsc : Forall (fun x => below c' x /\ consistent x) sc.
      apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
      exact: (below_mono _ _ _ Y1 Hc').
    by case: (svr); repeat constructor; auto; rewrite /=; lia.
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k))
        (bW (VInfo k Integer None) (VInfo (S k) Real None)) p ->
      live_value k
        (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
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
  have Hsc' : scope_ok (sx :: ix :: L) (S c) wP PScalar
      (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
      (DBound (c, c) :: sc2) wr2.
    split.
      by constructor; [split=> /=; [lia | by []] | apply: Hb2; lia].
    split; first by move=> y Hy; right; apply: Hwr2.
    split; last by move=> o E.
    move=> p [<- | [<- | Hp]] Lp.
    - by rewrite /sc2; destruct svr; rewrite /=; split; auto.
    - by split; [left |].
    have [R1 R2] := Hr p Hp (Hlive_b p Hp Lp).
    by split; [right; apply: Hsc2 | move=> Hd; right; apply: Hsc2; apply: R2].
  have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) wP PScalar Replay
            (bA (pa ix) (pa sx))
            (bW (VInfo k Integer None) (VInfo (S k) Real None))
            (bT (pt ix) (pt sx)) Real (DBound (c, c) :: sc2) wr2
            (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) Hs' Hsc' I HtB.
  rewrite Hob => -[Hc2 Hg].
  have Hn2 : In n wr2 /\ (In (DotOf n) wr2 \/ svr = false).
    by rewrite /wr2; case: (svr) => /=; auto.
  have Hbody : good (DBound (c, c) :: sc2) wr2
                 (sb ++ (if svr then [DAssign (DVar n) vb;
                                      DAssign (DVar (DotOf n)) db]
                         else [DAssign (DVar n) vb]))%list.
    apply: Hg => sc' wr' J1 J2' _ _ [Q1 Q2].
    apply: good_assign_end;
      [apply: J2'; exact: (proj1 Hn2) | | exact: Q1 | exact: Q2].
    by case: (proj2 Hn2) => [Hq | Hq]; [left; apply: J2' | right].
  have Hin2 : ~ In (DBound (c, c)) sc2.
    rewrite /sc2 /n; case: (svr) => /= Hin;
      repeat match type of Hin with _ \/ _ =>
        destruct Hin as [E | Hin];
        [first [discriminate E | inversion E; lia] |] end;
      contradiction.
  have HL1 : expr_ok sc2 (spell (amap pt loP)).
    by apply: (expr_ok_incl sc) Hsc2 _; apply/expr_ok_allv.
  have HH1 : expr_ok sc2 (spell (amap pt hiP)).
    by apply: (expr_ok_incl sc) Hsc2 _; apply/expr_ok_allv.
  split; first lia.
  move=> rest Hrest; rewrite /tan_fold; destruct svr eqn:Hsvr; rewrite /=.
    apply: GoodMutable; [by apply/expr_ok_allv | exact: N1 | by [] |].
    apply: GoodMutable; [| by case | by [] |].
      apply: (expr_ok_incl sc); first by move=> y Hy; right.
      by apply/expr_ok_allv.
    apply: GoodFor;
      [exact: Hin2 | by [] | exact: HL1 | exact: HH1 | exact: Hbody |].
    apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
                   exact: Hwr2 |].
    by split=> /=; auto.
  apply: GoodMutable; [by apply/expr_ok_allv | exact: N1 | by [] |].
  apply: GoodFor;
    [exact: Hin2 | by [] | exact: HL1 | exact: HH1 | exact: Hbody |].
  apply: Hrest; [exact: Hsc2 | by move=> y Hy /=; auto | apply: Hb2; lia |
                 exact: Hwr2 |].
  by split=> /=; auto.
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
             (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)))
  Htc => [tb [| mm]] Htc; rewrite /= in Htc; try discriminate.
case Etb: (ty_eqb tb (Array z)) Htc => Htc; rewrite /= in Htc; try discriminate.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k)))) Htc
  => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => Ete; subst te.
rewrite /= Eat in Hst; case: Hst => Ej _; subst j.
have Hlivo : live_value k (AFold Bare (amap pw loP) (amap pw hiP)
                             (AVar (pw o)) bW) o.
  by case: (Hlv o (or_intror (or_intror erefl))).
have Hvo : avaried (pa o) = true.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hown; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate.
    destruct (vty (pw y)); try discriminate.
    case: Hown => Ey; subst y.
    have Hia : is_array (vty (pw o)) by rewrite Eat.
    have [_ Hv] := s_top _ _ _ _ _ _ _ Hs o erefl erefl Hia.
    exact: Hv Hlivo.
  case: Hown => Eo; subst sx0.
  by have [_ [_ [_ [_ [Hv _]]]]] := s_place _ _ _ _ _ _ _ Hs.
have Hsvr : svr = true by rewrite /svr /fold_varied /= Hvo.
have [W1 W2] := Ho o Hown.
cbn [open_pairs]; rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
cbn [open_pairs].
change (varied (amap pa (AVar o)) ||
        varied_anf (S (S k)) (bA (fresh k) (fresh (S k)))) with svr.
set n := DBound (pn o, pn o) in Hob *.
set ix := PV (AV k false) (VInfo k Integer None)
            (TVar (DBound (c, c)) Integer None false false false false None)
            (VInt 0) c.
set sx := PV (AV (S k) svr) (VInfo (S k) (Array z) None)
            (TVar n (Array z) None svr svr svr false None)
            (default_dual (Array z)) (pn o).
have Hlive_b : forall p, In p L ->
    live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
      p ->
    live_value k (AFold Bare (amap pw loP) (amap pw hiP) (AVar (pw o)) bW) p /\
    p <> o.
  move=> p Hp Hl.
  have E2 := live_cont2 L k bP bW (pfresh k) (pfresh (S k))
               (VInfo k Integer None) (VInfo (S k) (Array z) None) (vid (pw p))
               HbW HL erefl erefl erefl erefl.
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
have Hcons : Forall (fun x => below (S c) x /\ consistent x)
               (DBound (c, c) :: sc).
  constructor; first by split=> /=; [lia | by []].
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
have Hsc' : scope_ok (sx :: ix :: L) (S c) wP (PArray ix sx)
    (live_anf (S (S k)) (bW (VInfo k Integer None)
                            (VInfo (S k) (Array z) None)))
    (DBound (c, c) :: sc) wr.
  split; first exact: Hcons.
  split; first by move=> y Hy; right; apply: Hw.
  split.
    move=> p [<- | [<- | Hp]] Lp.
    - by split; [right; apply: Hw | move=> _; right; apply: Hw].
    - by split; [left |].
    have [Hl' _] := Hlive_b p Hp Lp; have [R1 R2] := Hr p Hp Hl'.
    by split; [right | move=> Hd; right; apply: R2].
  by move=> o' Ho2; rewrite /= in Ho2; case: Ho2 => Eo2; subst o'; split.
have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) Replay
          (bA (pa ix) (pa sx))
          (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
          (bT (pt ix) (pt sx)) (Array z) (DBound (c, c) :: sc) wr
          (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) Hs' Hsc' I HtB.
rewrite Hob => -[Hc2 Hg].
split; first lia.
move=> rest Hrest /=.
apply: GoodFor; [exact: Hni | by [] | by apply/expr_ok_allv |
                 by apply/expr_ok_allv | |].
  by rewrite -(app_nil_r sb); apply: Hg => *; constructor.
apply: Hrest; [exact: incl_refl | exact: incl_refl | | exact: Hw |].
  apply: (Forall_impl _ _ Hb) => y [Y1 Y2]; split=> //.
  by apply: (below_mono c _ _ Y1); lia.
by split; [apply: Hw | move=> _; apply: Hw].
Qed.

(* The discipline holds for every body and every value. *)
Theorem scoping :
  (forall bP : anf pv bare, good_body bP) /\ (forall eP : value pv bare, good_value eP).
Proof.
apply: anf_value_ind.
- by move=> a e IHe b IHb; case: a => *; apply: good_let.
- by move=> a; apply: good_ret.
- by move=> f a; apply: good_op1.
- by move=> f a b; apply: good_op2.
- by move=> a i; apply: good_get.
- by move=> a i v; apply: good_set.
- by move=> c t IHt e IHe; apply: good_ite.
- by move=> lo hi b IHb; apply: good_map.
by move=> a lo hi init b IHb; apply: good_fold.
Qed.
