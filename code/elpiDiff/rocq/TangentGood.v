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
  intros H1 H2 rest Hr; rewrite <- app_assoc; apply H1.
  intros sc1 wr1 I1 I2 Hb Hw HQ; apply (H2 sc1 wr1 I1 I2 Hb Hw HQ).
  intros sc2 wr2 J1 J2 Hb2 Hw2 HQ2; apply Hr; auto; [intros x Hx; apply J1, I1, Hx | intros x Hx; apply J2, I2, Hx].
Qed.

Lemma good_k_nil sc wr c (Q : list (dvar W) -> list (dvar W) -> Prop) :
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc -> Q sc wr -> good_k sc wr c [] Q.
Proof. intros Hb Hw HQ rest Hr; apply Hr; auto; apply incl_refl. Qed.

(* The scope of a body: the variables opened before c, which hold the
   variables in scope the body reads and the storage it updates in place. *)
Definition scope_ok (L : list pv) (c : nat) (wP : option (atom pv)) (pp : pplace)
  (live : pv -> Prop) (sc wr : list (dvar W)) : Prop :=
  Forall (fun x => below c x /\ consistent x) sc /\ incl wr sc /\
  (forall p, In p L -> live p -> In (stored p) sc /\ (tdot (pt p) = true -> In (DotOf (stored p)) sc)) /\
  (forall o, owner wP pp = Some o -> In (stored o) wr /\ In (DotOf (stored o)) wr).

Definition notape (ss : list (dstmt W)) : Prop := existsb has_tape_op ss = false.

Definition good_body (bP : anf pv bare) : Prop :=
  forall L k c wP pp m bA bW bT ty sc wr,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT ->
  sctx L k c wP pp (live_anf k bW) ty -> scope_ok L c wP pp (live_anf k bW) sc wr -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  let '((ss, (ve, de)), c') :=
    open_pairs (tan W (option_map (amap pt) wP) (rebuild _ bT (annotate_body_t false m k bA))) c in
  (c <= c')%nat /\ notape ss /\ good_k sc wr c' ss (fun sc' _ => expr_ok sc' ve /\ expr_ok sc' de).

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
  (c <= c')%nat /\ notape se /\
  good_k sc wr c' se (fun sc' _ => In n sc' /\ (vr = true -> In (DotOf n) sc')).

(* A body that returns an atom: no statement. *)
Lemma good_ret (aP : atom pv) : good_body (ARet aP).
Proof.
  intros L k c wP pp m bA bW bT ty sc wr HA HW HT Hs [Hb [Hw [Hr Ho]]] Hty Htc.
  destruct bA as [| aA], bW as [| aW], bT as [| aT]; simpl in HA, HW, HT; try contradiction.
  apply atom_graph in HT as [-> HT]; apply atom_graph in HW as [-> HW].
  simpl; split; [lia | split; [reflexivity |]].
  apply good_k_nil; auto.
  destruct aP as [p | |]; simpl; auto.
  assert (Hl : live_anf k (ARet (amap pw (AVar p))) p) by (unfold live_anf; simpl; apply Nat.eqb_refl).
  destruct (Hr p (HT p eq_refl) Hl) as [R1 R2].
  destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HT p eq_refl)) as [_ [_ [Hst [_ [_ [Hd _]]]]]].
  rewrite Hst; split; [exact R1 |]; destruct (tdot (pt p)) eqn:Et; simpl; auto.
Qed.

(* ---------------------------------------------------------------------------
   Expressions in scope: every variable they read is in scope. *)

Definition allv (P : dvar W -> Prop) (e : dexpr W) : Prop := forall x, In x (dvars e) -> P x.

Lemma expr_ok_allv sc e : expr_ok sc e <-> allv (fun x => In x sc) e.
Proof.
  unfold allv; induction e as [x | l | z | a IHa i IHi | f a IHa | f a IHa b IHb]; simpl.
  - split; [intros H y [<- | []]; exact H | intros H; apply H; auto].
  - split; [intros _ y [] | auto].
  - split; [intros _ y [] | auto].
  - rewrite IHa, IHi; split; [intros [H1 H2] y Hy; apply in_app_or in Hy as [Hy | Hy]; auto
                             | intros H; split; intros y Hy; apply H, in_or_app; auto].
  - exact IHa.
  - rewrite IHa, IHb; split; [intros [H1 H2] y Hy; apply in_app_or in Hy as [Hy | Hy]; auto
                             | intros H; split; intros y Hy; apply H, in_or_app; auto].
Qed.

Lemma expr_ok_incl sc sc' e : incl sc sc' -> expr_ok sc e -> expr_ok sc' e.
Proof. intros I; rewrite !expr_ok_allv; intros H x Hx; apply I, H, Hx. Qed.

Lemma allv_op1 P f e : allv P e -> allv P (DOp1 f e).
Proof. auto. Qed.
Lemma allv_op2 P f e1 e2 : allv P e1 -> allv P e2 -> allv P (DOp2 f e1 e2).
Proof. intros H1 H2 x Hx; simpl in Hx; apply in_app_or in Hx as [Hx | Hx]; auto. Qed.
Lemma allv_at P e1 e2 : allv P e1 -> allv P e2 -> allv P (DAt e1 e2).
Proof. intros H1 H2 x Hx; simpl in Hx; apply in_app_or in Hx as [Hx | Hx]; auto. Qed.
Lemma allv_lit P l : allv P (DReal l).
Proof. intros x []. Qed.
Lemma allv_int P z : allv P (DInt z).
Proof. intros x []. Qed.
Lemma allv_scale P p e : allv P p -> allv P e -> allv P (scale p e).
Proof.
  intros H1 H2; destruct p; try (apply allv_op2; auto); unfold scale.
  destruct (String.eqb s "1"); [exact H2 |]; destruct (String.eqb s "-1"); [apply allv_op1, H2 |].
  apply allv_op2; auto.
Qed.
Lemma allv_sum P l : Forall (allv P) l -> allv P (sum l).
Proof.
  induction 1 as [| e l He Hl IH]; [apply allv_lit |]; simpl.
  destruct l; [exact He | apply allv_op2; auto].
Qed.

Lemma allv_partial1 P f (a : atom (tvar W)) p :
  allv P (spell a) -> allv P (dot a) -> partial1 f a = Some p -> allv P (scale (spell_partial p) (dot a)).
Proof.
  intros Hs Hd Hp; apply allv_scale; [| exact Hd].
  destruct f as [| | | | | | z |]; simpl in Hp; try discriminate;
    try (destruct z); injection Hp as <-; simpl;
    repeat (apply allv_op1 || apply allv_op2 || apply allv_lit || assumption).
Qed.

Lemma allv_partial2 P f (a b : atom (tvar W)) pa pb :
  allv P (spell a) -> allv P (dot a) -> allv P (spell b) -> allv P (dot b) ->
  partial2 f a b = Some (pa, pb) -> allv P (sum (tangent_term W a pa ++ tangent_term W b pb)).
Proof.
  intros Hsa Hda Hsb Hdb Hp; apply allv_sum; unfold tangent_term.
  destruct f; simpl in Hp; try discriminate; injection Hp as <- <-;
    destruct (tvaried_atom a), (tvaried_atom b); simpl;
    repeat (apply Forall_cons || apply Forall_nil || apply allv_scale || apply allv_op1
            || apply allv_op2 || apply allv_lit || assumption).
Qed.

(* An atom of a value, in scope. *)
Lemma atom_in_scope k sc (aP : atom pv) :
  (forall p, aP = AVar p -> static_ok k p /\ In (stored p) sc /\ (tdot (pt p) = true -> In (DotOf (stored p)) sc)) ->
  allv (fun x => In x sc) (spell (amap pt aP)) /\ allv (fun x => In x sc) (dot (amap pt aP)).
Proof.
  intros H; destruct aP as [p | |]; simpl; try (split; intros x []; fail).
  destruct (H p eq_refl) as [[_ [_ [Hst _]]] [H1 H2]]; rewrite Hst; split.
  - intros x [<- | []]; exact H1.
  - destruct (tdot (pt p)) eqn:Et; simpl; [intros x [<- | []]; auto | intros x []].
Qed.

(* ---------------------------------------------------------------------------
   The operations: definitions of new constants. *)

Lemma good_constants j c sc wr (t : ty) e1 e2 (Q : list (dvar W) -> list (dvar W) -> Prop) :
  expr_ok sc e1 -> expr_ok sc e2 -> ~ In (DBound (j, j)) sc -> ~ In (DotOf (DBound (j, j))) sc -> (j < c)%nat ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  Q (DotOf (DBound (j, j)) :: DBound (j, j) :: sc) wr ->
  good_k sc wr c [DDefine (DConstant t) (DBound (j, j)) e1; DDefine (DConstant Real) (DotOf (DBound (j, j))) e2] Q.
Proof.
  intros H1 H2 N1 N2 Hj Hb Hw HQ rest Hr; simpl.
  apply GoodConstant; [exact H1 | exact N1 | reflexivity |].
  apply GoodConstant; [apply (expr_ok_incl sc); [intros x Hx; right; exact Hx | exact H2]
                      | intros [E | E]; [discriminate | contradiction] | reflexivity |].
  apply Hr; [intros x Hx; right; right; exact Hx | apply incl_refl | | intros x Hx; right; right; auto | exact HQ].
  constructor; [simpl; split; [lia | reflexivity] |]; constructor; [simpl; split; [lia | reflexivity] | exact Hb].
Qed.

Lemma good_constant j c sc wr (t : ty) e1 (Q : list (dvar W) -> list (dvar W) -> Prop) :
  expr_ok sc e1 -> ~ In (DBound (j, j)) sc -> (j < c)%nat ->
  Forall (fun x => below c x /\ consistent x) sc -> incl wr sc ->
  Q (DBound (j, j) :: sc) wr ->
  good_k sc wr c [DDefine (DConstant t) (DBound (j, j)) e1] Q.
Proof.
  intros H1 N1 Hj Hb Hw HQ rest Hr; simpl.
  apply GoodConstant; [exact H1 | exact N1 | reflexivity |].
  apply Hr; [intros x Hx; right; exact Hx | apply incl_refl | | intros x Hx; right; auto | exact HQ].
  constructor; [simpl; split; [lia | reflexivity] | exact Hb].
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
  intros Hs Hr Ha; apply (atom_in_scope k); intros p E; destruct (Ha p E) as [Hp Lp].
  split; [exact (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp) | exact (Hr p Hp Lp)].
Qed.

Lemma good_op1 f (aP : atom pv) : good_value (AOp1 f aP).
Proof.
  gvalue_intro; simpl in Htc, Hst |- *; rename f2 into g.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AOp1 g (amap pw aP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; apply Nat.eqb_refl]).
  destruct (operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv) as [A1 A2].
  destruct Hst as [N1 N2].
  destruct (varied (amap pa aP)); simpl; (split; [lia | split; [reflexivity |]]).
  - apply good_constants; auto.
    + apply expr_ok_allv, allv_op1, A1.
    + apply expr_ok_allv; destruct (partial1 g (amap pt aP)) as [p |] eqn:Hp; [| apply allv_lit].
      unfold tangent_term; destruct (tvaried_atom (amap pt aP)); [| apply allv_lit].
      apply allv_sum; constructor; [apply (allv_partial1 _ g _ p); auto | constructor].
    + split; [right; left; reflexivity | intros _; left; reflexivity].
  - apply good_constant; auto.
    + apply expr_ok_allv, allv_op1, A1.
    + split; [left; reflexivity | discriminate].
Qed.

Lemma good_op2 f (aP bP : atom pv) : good_value (AOp2 f aP bP).
Proof.
  gvalue_intro; simpl in Htc, Hst |- *; rename f2 into g.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AOp2 g (amap pw aP) (amap pw bP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity]).
  assert (Hlv' : forall p, bP = AVar p -> In p L /\ live_value k (AOp2 g (amap pw aP) (amap pw bP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl, orb_true_r; reflexivity]).
  destruct (operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv) as [A1 A2].
  destruct (operand_scope _ _ _ _ _ _ _ _ bP Hs Hr Hlv') as [B1 B2].
  destruct Hst as [N1 N2].
  destruct (if comparison g then false else varied (amap pa aP) || varied (amap pa bP)); simpl;
    (split; [lia | split; [reflexivity |]]).
  - apply good_constants; auto.
    + apply expr_ok_allv, allv_op2; auto.
    + apply expr_ok_allv; destruct (partial2 g (amap pt aP) (amap pt bP)) as [[qa qb] |] eqn:Hp;
        [apply (allv_partial2 _ g _ _ qa qb); auto | apply allv_lit].
    + split; [right; left; reflexivity | intros _; left; reflexivity].
  - apply good_constant; auto.
    + apply expr_ok_allv, allv_op2; auto.
    + split; [left; reflexivity | discriminate].
Qed.

Lemma good_get (aP iP : atom pv) : good_value (AGet aP iP).
Proof.
  gvalue_intro; simpl in Htc, Hst |- *.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity]).
  assert (Hlv' : forall p, iP = AVar p -> In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl, orb_true_r; reflexivity]).
  destruct (operand_scope _ _ _ _ _ _ _ _ aP Hs Hr Hlv) as [A1 A2].
  destruct (operand_scope _ _ _ _ _ _ _ _ iP Hs Hr Hlv') as [B1 B2].
  destruct Hst as [N1 N2].
  rewrite (tvaried_amap k aP).
  2: { intros p E; apply (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs)), Hlv, E. }
  destruct (varied (amap pa aP)); simpl; (split; [lia | split; [reflexivity |]]).
  - apply good_constants; auto.
    + apply expr_ok_allv, allv_at; auto.
    + apply expr_ok_allv, allv_at; auto.
    + split; [right; left; reflexivity | intros _; left; reflexivity].
  - apply good_constant; auto.
    + apply expr_ok_allv, allv_at; auto.
    + split; [left; reflexivity | discriminate].
Qed.

Lemma good_set (aP iP vP : atom pv) : good_value (ASet aP iP vP).
Proof.
  gvalue_intro; simpl in Htc |- *.
  destruct pp as [| | | ix sx]; simpl in Htc; try discriminate.
  destruct (of_atom (amap pw aP)) as [| | | z] eqn:Eat; try discriminate.
  destruct tail; simpl in Htc; [| discriminate].
  destruct aP as [a | |]; simpl in Htc, Eat; try discriminate.
  destruct ((vid (pw a) =? vid (pw sx))%nat) eqn:Ea; simpl in Htc; [| discriminate].
  pose proof (s_place _ _ _ _ _ _ _ Hs) as [Hix [Hsx _]].
  assert (Ha : In a L) by auto.
  pose proof (same_vid_s _ _ _ _ _ _ _ _ _ Hs Ha Hsx Ea); subst a.
  simpl in Hst; injection Hst as Ej; subst j.
  destruct (Ho sx eq_refl) as [W1 W2].
  assert (Hlv : forall p, iP = AVar p \/ vP = AVar p ->
            In p L /\ live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p)
    by (intros p [E | E]; subst; split; auto; unfold live_value; simpl;
        rewrite Nat.eqb_refl, ?orb_true_r; reflexivity).
  destruct (operand_scope _ _ _ _ _ _ _ _ iP Hs Hr (fun p E => Hlv p (or_introl E))) as [I1 I2].
  destruct (operand_scope _ _ _ _ _ _ _ _ vP Hs Hr (fun p E => Hlv p (or_intror E))) as [V1 V2].
  destruct (varied (amap pa (AVar sx)) || varied (amap pa vP)); simpl; (split; [lia | split; [reflexivity |]]);
    intros rest Hrest; simpl.
  - apply GoodAssign; [split; [exact W1 | apply expr_ok_allv, I1] | apply expr_ok_allv, V1 |].
    apply GoodAssign; [split; [exact W2 | apply expr_ok_allv, I1] | apply expr_ok_allv, V2 |].
    apply (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw); split; [apply Hw, W1 | intros _; apply Hw, W2].
  - apply GoodAssign; [split; [exact W1 | apply expr_ok_allv, I1] | apply expr_ok_allv, V1 |].
    apply (Hrest sc wr (incl_refl _) (incl_refl _) Hb Hw); split; [apply Hw, W1 | discriminate].
Qed.

(* ---------------------------------------------------------------------------
   A let. *)

Lemma sctx_weaken L k c c' wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  sctx L k c' wP pp live' ty.
Proof.
  intros Hc Hl Hcc; destruct Hc as [HS HU HN HW HP HO HA HT HTop]; constructor; auto.
  - intros p Hp; specialize (HN p Hp); lia.
  - intros o p Ho Hp E; destruct (HO o p Ho Hp E) as [H | H]; [left; exact H | right; auto].
  - intros y H1 H2 H3; destruct (HTop y H1 H2 H3) as [A B]; auto.
Qed.

Lemma scope_weaken L c c' wP pp (live live' : pv -> Prop) sc wr :
  scope_ok L c wP pp live sc wr -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  scope_ok L c' wP pp live' sc wr.
Proof.
  intros [Hb [Hw [Hr Ho]]] Hl Hc; split; [| split; [exact Hw | split; [| exact Ho]]].
  - apply Forall_impl with (P := fun x => below c x /\ consistent x); auto.
    intros x [H1 H2]; split; [apply (below_mono c); auto | exact H2].
  - intros p Hp Lp; apply Hr; auto.
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
  destruct t; simpl; split; auto; [apply repeat_length |].
  apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst; reflexivity.
Qed.

(* A varied value is a real or an array. *)
Lemma varied_real_or_array L k wW pW tail (eP : value pv bare) eA eW te :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L ->
  typecheck_value wW pW tail k eW = (te, Ok) -> varied_value k eA = true -> real_or_array te.
Proof.
  intros HA HW HL Htc Hv.
  destruct eP, eA, eW; simpl in HA, HW; try contradiction;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : atom_eq (gA L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    end; subst; simpl in Htc, Hv.
  - destruct f1; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - destruct (comparison f1) eqn:Hcmp; [discriminate |].
    crush_match Htc; injection Htc as <-.
    assert (Hra : forall aP : atom pv, (forall p, aP = AVar p -> In p L) -> varied (amap pa aP) = true ->
                  real_or_array (of_atom (amap pw aP))).
    { intros aP Ha Hva; destruct aP as [q | |]; simpl in Hva |- *; try discriminate.
      destruct (static_in _ _ _ HL (Ha q eq_refl)) as [E1 [_ [_ [_ [_ [_ [_ [H' _]]]]]]]]; apply H'; exact Hva. }
    apply orb_true_iff in Hv as [Hv | Hv];
      [pose proof (Hra a H0 Hv) as Hr' | pose proof (Hra b H1 Hv) as Hr'];
      destruct f1; simpl in Hcmp; try discriminate; unfold operation2_typed in Heqo0;
      destruct (of_atom (amap pw a)), (of_atom (amap pw b)); simpl in *; try contradiction; try discriminate;
      injection Heqo0 as <- _; exact I.
  - crush_match Htc; injection Htc as <-; exact I.
  - destruct pW; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - destruct pW; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - destruct pW; simpl in Htc; try (crush_match Htc; fail).
    destruct tail; [| crush_match Htc].
    destruct lo, hi; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - crush_match Htc; injection Htc as <-; exact I.
Qed.

Lemma good_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  good_value eP -> (forall x, good_body (cP x)) -> good_body (ALet a eP cP).
Proof.
  intros IHe IHb L k c wP pp m bA bW bT ty sc wr HA HW HT Hs Hsc Hty Htc.
  destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |];
    simpl in HA, HW, HT; try contradiction.
  destruct HA as [HeA HcA], HW as [HeW HcW], HT as [HeT HcT].
  simpl in Htc.
  destruct (typecheck_value (option_map (amap pw) wP) (wplace pp) (WellFormed.is_tail cW k) k eW)
    as [te d0] eqn:Hte.
  destruct d0; simpl in Htc; [| discriminate].
  cbn [annotate_body_t]. destruct (needs false m (S k) (cA (let_binder k eA))) as [u l].
  set (vr := varied_value k eA). set (vt := annotate_value_t false k eA).
  set (rest := annotate_body_t false m (S k) (cA (let_binder k eA))).
  cbn [rebuild]. rewrite tan_let. cbv zeta.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
  destruct (open_with_storage L k wP eP eT vt (fun v0 => rebuild _ (cT v0) rest)
     (fun n rec => sbind (tan_value W (option_map (amap pt) wP) (rebuild_value _ eT vt) te vr n)
       (fun se => sbind (tan W (option_map (amap pt) wP) (rebuild _ (cT (open_let te n vr rec)) rest))
                    (fun '(sb, vd) => Done ((se ++ sb)%list, vd)))) c HeT HL) as [n [rec [c0 [Hopen Hn]]]].
  { intros a0 E; destruct (s_written _ _ _ _ _ _ _ Hs _ E) as [y [-> [Hy _]]]; eauto. }
  rewrite Hopen.
  rewrite <- (is_tail_transfer L k cP cW cT rest HcW HcT) in Hn by
    (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]]; auto).
  set (tail := WellFormed.is_tail cW k) in *.
  rewrite open_pairs_sbind.
  destruct (open_pairs (tan_value W (option_map (amap pt) wP) (rebuild_value (tvar W) eT vt) te vr n) c0)
    as [se c1] eqn:Hse.
  assert (Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p).
  { intros p H; unfold live_value, live_anf in *; simpl; rewrite H; reflexivity. }
  assert (Htail_ty : tail = true -> te = ty).
  { intros Ht; destruct (tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL eq_refl Ht) as [_ E].
    rewrite E in Htc; simpl in Htc; injection Htc; auto. }
  assert (Hnum : exists j, n = DBound (j, j) /\ (j < c0)%nat /\ (c <= c0)%nat /\
                 match storage wP tail eP with Some _ => True | None => j = c end).
  { destruct (storage wP tail eP) as [m0 |] eqn:Es; destruct Hn as [-> ->].
    - assert (Hsn : storage wP tail eP <> None) by (rewrite Es; discriminate).
      destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn))
        as [_ [o [Ho Es']]].
      rewrite Es in Es'; injection Es' as ->; exists (pn o); split; [reflexivity |].
      pose proof (s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho)); lia.
    - exists c; repeat split; lia. }
  destruct Hnum as [j [Ej [Hj0 [Hc0 Hjs]]]].
  destruct Hsc as [Hb [Hw [Hr Ho]]].
  assert (Hst : match storage wP tail eP with
                | Some m0 => n = m0
                | None => ~ In n sc /\ ~ In (DotOf n) sc
                end).
  { destruct (storage wP tail eP); [apply Hn |]; subst j; rewrite Ej.
    split; intros I; rewrite Forall_forall in Hb; destruct (Hb _ I) as [Hbl _]; simpl in Hbl; lia. }
  specialize (IHe L k c0 wP pp tail eA eW eT te n ty sc wr HeA HeW HeT
                (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlive_e Hc0)
                (scope_weaken _ _ _ _ _ _ _ _ _ (conj Hb (conj Hw (conj Hr Ho))) Hlive_e Hc0)
                Hte Htail_ty (ex_intro _ j (conj Ej Hj0)) Hst).
  cbv zeta in IHe; fold vr vt in IHe; rewrite Hse in IHe.
  destruct IHe as [Hc01 [Hnt1 Hgk1]].
  (* the variable of the let *)
  set (x := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec) (default_dual te) j).
  assert (Hx : aid (pa x) = k) by reflexivity.
  assert (HxL : ~ In x L) by exact (fresh_notin L k x (aids_below L k HL) Hx).
  assert (Hvid : forall p, In p L -> (vid (pw p) < k)%nat)
    by (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [H _]]; exact H).
  rewrite open_pairs_sbind.
  destruct (storage wP tail eP) as [m0 |] eqn:Es.
  - (* stored in place: the rest only returns the variable *)
    assert (Hsn : storage wP tail eP <> None) by (rewrite Es; discriminate).
    destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn)) as [Ht [o [Ho' Es']]].
    rewrite Es in Es'; injection Es' as Em0; subst m0.
    destruct (tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht) as [Hcx EW].
    assert (ET : cT (pt x) = ARet (AVar (pt x))).
    { specialize (HcT x (pt x)); rewrite Hcx in HcT.
      destruct (cT (pt x)) as [? ? ? | [t' | |]]; simpl in HcT; try contradiction.
      destruct HcT as [E | I]; [injection E as E; rewrite <- E; reflexivity | apply in_gT in I as [I _]; contradiction]. }
    simpl in ET; rewrite ET; simpl.
    split; [lia | split; [rewrite app_nil_r; exact Hnt1 |]].
    rewrite app_nil_r; intros rest' Hrest.
    apply Hgk1; intros sc1 wr1 I1 I2 Hb1 Hw1 [Q1 Q2]; apply Hrest; auto.
    simpl; split; [exact Q1 |]; destruct vr; simpl; [apply Q2; reflexivity | exact I].
  - (* a fresh variable *)
    destruct Hn as [-> Hc0']; subst j.
    assert (Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
                                live_anf k (ALet aW eW cW) p).
    { unfold live_anf; intros p Hp H; simpl.
      rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx eq_refl) in H.
      rewrite H; apply orb_true_r. }
    set (cW' := cW (VInfo k te None)).
    assert (Hxs : static_ok (S k) x).
    { destruct (default_dual_ok te) as [D1 D2].
      repeat split; simpl; auto; try lia; try discriminate.
      intros Hv; exact (varied_real_or_array _ _ _ _ _ _ _ _ _ HeA HeW HL Hte Hv). }
    assert (Hs' : sctx (x :: L) (S k) c1 wP pp (live_anf (S k) cW') ty).
    { constructor.
      - constructor; [exact Hxs |]; apply Forall_impl with (P := static_ok k); auto.
        intros p Hp; apply (static_mono k); auto.
      - intros p q [<- | Hp] [<- | Hq] E; auto.
        + specialize (Hvid _ Hq); simpl in E; lia.
        + specialize (Hvid _ Hp); simpl in E; lia.
        + exact (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
      - intros p [<- | Hp]; simpl; [lia |].
        pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp); lia.
      - intros a0 E; destruct (s_written _ _ _ _ _ _ _ Hs _ E) as [y [-> [Hy Hv]]].
        exists y; split; [reflexivity | split; [right; exact Hy | exact Hv]].
      - pose proof (s_place _ _ _ _ _ _ _ Hs) as Hp; destruct pp; simpl in *; auto.
        destruct Hp as [A [B C]]; split; [right; exact A | split; [right; exact B | exact C]].
      - intros o p Ho' [<- | Hp] Ep.
        + pose proof (s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho')); simpl in Ep; lia.
        + destruct (s_owner _ _ _ _ _ _ _ Hs o p Ho' Hp Ep) as [H | H]; [left; exact H |].
          right; intros Hl; apply H, Hlive_c; auto.
      - intros p o [<- | Hp] Lp Ha Hg Ho'.
        + destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_intror Ha))
            as [_ [o' [_ Es']]].
          rewrite Es in Es'; discriminate.
        + exact (s_arrays _ _ _ _ _ _ _ Hs p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho').
      - exact (s_ty _ _ _ _ _ _ _ Hs).
      - intros y Hpp Hw' Ha.
        destruct (s_written _ _ _ _ _ _ _ Hs _ Hw') as [y' [E [Hy _]]]; injection E as <-.
        destruct (s_top _ _ _ _ _ _ _ Hs y Hpp Hw' Ha) as [T1 T2].
        split; [exact T1 | intros Ly; apply T2, Hlive_c; auto]. }
    assert (Hsc' : forall sc1 wr1, incl sc sc1 -> incl wr wr1 ->
                   Forall (fun x0 => below c1 x0 /\ consistent x0) sc1 -> incl wr1 sc1 ->
                   In (DBound (c, c)) sc1 -> (vr = true -> In (DotOf (DBound (c, c))) sc1) ->
                   scope_ok (x :: L) c1 wP pp (live_anf (S k) cW') sc1 wr1).
    { intros sc1 wr1 I1 I2 Hb1 Hw1 Q1 Q2; split; [exact Hb1 | split; [exact Hw1 | split]].
      - intros p [<- | Hp] Hl; [split; [exact Q1 | exact Q2] |].
        destruct (Hr p Hp (Hlive_c p Hp Hl)) as [R1 R2]; split; [apply I1, R1 | intros Hd; apply I1, R2, Hd].
      - intros o Ho'; destruct (Ho o Ho') as [W1 W2]; split; apply I2; auto. }
    specialize (IHb x).
    destruct (open_pairs (tan W (option_map (amap pt) wP)
               (rebuild (tvar W) (cT (open_let te (DBound (c, c)) vr rec)) rest)) c1)
      as [[sb [ve' de']] c2] eqn:Hsb.
    match goal with |- context [open_pairs ?t c1] =>
      replace (open_pairs t c1) with ((sb, (ve', de')), c2) by (rewrite <- Hsb; reflexivity) end.
    simpl.
    assert (Hsc0 : scope_ok (x :: L) c1 wP pp (live_anf (S k) cW')
                     (DBound (c, c) :: DotOf (DBound (c, c)) :: sc) wr).
    { apply Hsc'; auto.
      - intros y Hy; right; right; exact Hy.
      - apply incl_refl.
      - constructor; [simpl; split; [lia | reflexivity] |]; constructor; [simpl; split; [lia | reflexivity] |].
        apply Forall_impl with (P := fun x0 => below c x0 /\ consistent x0); auto.
        intros y [H1 H2]; split; [apply (below_mono c); auto; lia | exact H2].
      - intros y Hy; right; right; apply Hw, Hy.
      - left; reflexivity.
      - intros _; right; left; reflexivity. }
    pose proof (IHb (x :: L) (S k) c1 wP pp m (cA (pa x)) cW' (cT (pt x)) ty _ _
                  (HcA x _) (HcW x _) (HcT x _) Hs' Hsc0 Hty Htc) as IH0.
    unfold x in IH0; cbn [pt pa] in IH0; fold rest in IH0.
    match type of IH0 with context [open_pairs ?t c1] =>
      replace (open_pairs t c1) with ((sb, (ve', de')), c2) in IH0 by (rewrite <- Hsb; reflexivity) end.
    destruct IH0 as [Hc12 [Hnt2 _]].
    split; [lia | split; [unfold notape; rewrite existsb_app, Hnt1; exact Hnt2 |]].
    apply (good_k_app sc wr c1 c2 se sb _ _ Hgk1).
    intros sc1 wr1 I1 I2 Hb1 Hw1 [Q1 Q2].
    pose proof (IHb (x :: L) (S k) c1 wP pp m (cA (pa x)) cW' (cT (pt x)) ty sc1 wr1
                  (HcA x _) (HcW x _) (HcT x _) Hs' (Hsc' sc1 wr1 I1 I2 Hb1 Hw1 Q1 Q2) Hty Htc) as IH1.
    unfold x in IH1; cbn [pt pa] in IH1; fold rest in IH1.
    match type of IH1 with context [open_pairs ?t c1] =>
      replace (open_pairs t c1) with ((sb, (ve', de')), c2) in IH1 by (rewrite <- Hsb; reflexivity) end.
    exact (proj2 (proj2 IH1)).
Qed.
