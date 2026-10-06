(* DualsDerive.v — theorem 3: where a program is defined, it is
   differentiable, and the dual numbers compute its derivative.

   The program f (L0) computes, from its arguments x, a value; its real
   arguments (the reals, and the elements of the arrays) are the variables,
   its integer and boolean arguments are fixed as in x. `value_of f x` is
   that function, from R^n to R^m (n reals in, m reals out), and `defined f x`
   (Smooth.v) is the hypothesis of Abadi and Plotkin: the evaluation of f at
   x over the reals compares no two equal reals and applies no operation
   where it is not differentiable.

   Differentiability is Fréchet's, in Coquelicot's formulation: `filterdiff
   g (locally x) dg` says that dg is a linear map (`is_linear`) and that
   g (x + h) = g x + dg h + o(|h|). The spaces R^n are those of Euclidean.v.

   The proof evaluates f in a domain of numbers of its own (`families`): a
   number is a function of the point (y in a normed module E) together with
   its derivative at the point of interest e0, a pair (r, dr). An operation
   composes the functions and computes the derivative by the chain rule,
   exactly as the dual numbers compute their tangents (Domain.v), and fails
   where smooth_reals fails at e0. Then:
   - (reflection) where the evaluation over smooth_reals succeeds at e0, the
     evaluation over the families succeeds, with the same value at e0;
   - (goodness) every family computed is differentiable at e0, with the
     derivative it carries (`good`);
   - (dual numbers) the dual numbers compute, exactly, the family at e0 with
     its derivative applied to a direction h: (r e0, dr h);
   - (points) at every y close enough to e0, the evaluation over the reals
     computes the families at y: the operations of the reals are total, and
     a comparison, strict at e0, keeps its outcome near e0 by continuity.
   The evaluators run at different instances of the PHOAS program, related
   by `parametric f` (Correctness.v).

   The main theorem, `duals_derive` (at the end), takes E = R^n, e0 the
   vector of the reals of x (`point_of x`), and as arguments the families
   `fam_args x`: the j-th real coordinate of x is the j-th coordinate
   function (linear, its own derivative), an element of a tape a constant.
   At y they give x with its reals replaced by y (`with_reals`); at e0, x;
   as dual numbers in the direction dx, the arguments `dual_args x dx`. The
   adapters `reals_of_args`, `with_reals`, `in_dim`, `out_dim`, `value_of`,
   `dual_args`, `primal_val` and `tangent_reals` state the theorem.

   Axioms: those of the Stdlib reals only (its Dedekind reals use
   sig_forall_dec and sig_not_dec; Rinv and total_order_T use functional
   extensionality; ln uses classic). *)

From Coquelicot Require Import Coquelicot.
From Stdlib Require Import String ZArith List QArith Qreals Reals DecimalString DecimalPos Lra Lia Ascii.
From ElpiDiff Require Import Syntax Domain Operations Eval Smooth Correctness Euclidean.

Import ListNotations.
Open Scope R_scope.

(* ---------------------------------------------------------------------------
   Literals. The partial derivatives of Domain.v use the literals "0", "1",
   "2", "-1", and that of an exponent k, spelled as the operations table does
   (`NilZero.string_of_int`); they read as the expected reals. *)

Lemma real_lit_Q s q : read_literal s = Some q -> real_lit s = Some (Q2R q).
Proof. unfold real_lit; intros ->; reflexivity. Qed.

Lemma real_lit_0 : real_lit "0" = Some 0.
Proof. rewrite (real_lit_Q _ 0%Q) by reflexivity; f_equal; unfold Q2R; simpl; field. Qed.
Lemma real_lit_1 : real_lit "1" = Some 1.
Proof. rewrite (real_lit_Q _ 1%Q) by reflexivity; f_equal; unfold Q2R; simpl; field. Qed.
Lemma real_lit_2 : real_lit "2" = Some 2.
Proof. rewrite (real_lit_Q _ 2%Q) by reflexivity; f_equal; unfold Q2R; simpl; field. Qed.
Lemma real_lit_m1 : real_lit "-1" = Some (-1).
Proof. rewrite (real_lit_Q _ (-1)%Q) by reflexivity; f_equal; unfold Q2R; simpl; field. Qed.

(* The digits of a decimal number, read from the left: the value of Pos.of_uint_acc. *)
Fixpoint digits_value (d : Decimal.uint) (m : Z) : Z :=
  match d with
  | Decimal.Nil => m
  | Decimal.D0 l => digits_value l (m * 10 + 0)
  | Decimal.D1 l => digits_value l (m * 10 + 1)
  | Decimal.D2 l => digits_value l (m * 10 + 2)
  | Decimal.D3 l => digits_value l (m * 10 + 3)
  | Decimal.D4 l => digits_value l (m * 10 + 4)
  | Decimal.D5 l => digits_value l (m * 10 + 5)
  | Decimal.D6 l => digits_value l (m * 10 + 6)
  | Decimal.D7 l => digits_value l (m * 10 + 7)
  | Decimal.D8 l => digits_value l (m * 10 + 8)
  | Decimal.D9 l => digits_value l (m * 10 + 9)
  end%Z.

Fixpoint digits_length (d : Decimal.uint) : nat :=
  match d with
  | Decimal.Nil => 0
  | Decimal.D0 l | Decimal.D1 l | Decimal.D2 l | Decimal.D3 l | Decimal.D4 l
  | Decimal.D5 l | Decimal.D6 l | Decimal.D7 l | Decimal.D8 l | Decimal.D9 l => S (digits_length l)
  end.

Lemma read_digits_uint d m k :
  read_digits (list_ascii_of_string (NilEmpty.string_of_uint d)) m k
  = (digits_value d m, (k + digits_length d)%nat, []).
Proof.
  revert m k; induction d; intros m k; simpl; try rewrite IHd. all: f_equal; f_equal; lia.
Qed.

Lemma digits_value_acc d p : digits_value d (Z.pos p) = Z.pos (Pos.of_uint_acc d p).
Proof.
  revert p; induction d; intros p; cbn [digits_value Pos.of_uint_acc]; try reflexivity;
    rewrite <- IHd; f_equal; rewrite ?Pos2Z.inj_add, ?Pos2Z.inj_mul; lia.
Qed.

Lemma digits_value_of_uint d : digits_value d 0 = Z.of_N (Pos.of_uint d).
Proof.
  induction d; simpl; try exact IHd; try reflexivity; apply digits_value_acc.
Qed.

(* the characters of a digit string are digits *)
Definition is_digit_char (c : ascii) : bool := match digit c with Some _ => true | None => false end.

Lemma uint_chars_digits d : forallb is_digit_char (list_ascii_of_string (NilEmpty.string_of_uint d)) = true.
Proof. induction d; simpl; auto. Qed.

Lemma to_uint_nonnil p : Pos.to_uint p <> Decimal.Nil.
Proof. intros H; generalize (Unsigned.of_to p); rewrite H; discriminate. Qed.

Lemma digit_not_space c : is_digit_char c = true -> c <> " "%char.
Proof. destruct c as [[] [] [] [] [] [] [] []]; try discriminate; intros _ H; discriminate H. Qed.

Lemma digit_not_slash c : is_digit_char c = true -> c <> "/"%char.
Proof. destruct c as [[] [] [] [] [] [] [] []]; try discriminate; intros _ H; discriminate H. Qed.

Lemma drop_nonspace c l : c <> " "%char ->
  (fix drop (l : list ascii) := match l with " "%char :: l' => drop l' | _ => l end) (c :: l) = c :: l.
Proof. destruct c as [[] [] [] [] [] [] [] []]; intros H; try reflexivity; now contradiction H. Qed.

Lemma strip_id l :
  (forall c, hd_error l = Some c -> c <> " "%char) ->
  (forall c, hd_error (rev l) = Some c -> c <> " "%char) -> strip l = l.
Proof.
  unfold strip; intros H1 H2; destruct l as [| c l]; [reflexivity |].
  rewrite drop_nonspace by (apply H1; reflexivity).
  destruct (rev (c :: l)) as [| d r] eqn:E; [apply (f_equal (@length _)) in E; rewrite length_rev in E; discriminate |].
  rewrite drop_nonspace by (apply H2; reflexivity).
  rewrite <- E, rev_involutive; reflexivity.
Qed.

Lemma split_digits l acc : forallb is_digit_char l = true ->
  (fix split (l acc : list ascii) : option (list ascii * list ascii) :=
     match l with
     | "/"%char :: l' => Some (rev acc, l')
     | c :: l' => split l' (c :: acc)
     | [] => None
     end) l acc = None.
Proof.
  revert acc; induction l as [| c l IH]; intros acc H; [reflexivity |].
  simpl in H; apply andb_prop in H as [Hc Hl].
  assert (Hs := digit_not_slash c Hc).
  destruct c as [[] [] [] [] [] [] [] []]; try (now contradiction Hs); apply IH; exact Hl.
Qed.

Lemma read_sign_digit c l : is_digit_char c = true -> read_sign (c :: l) = (1%Z, c :: l).
Proof. destruct c as [[] [] [] [] [] [] [] []]; try discriminate; reflexivity. Qed.

Lemma forallb_rev {A} (p : A -> bool) l : forallb p (rev l) = forallb p l.
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite forallb_app, IH; simpl; rewrite andb_true_r, andb_comm; reflexivity.
Qed.

Lemma hd_digit l c : forallb is_digit_char l = true -> hd_error l = Some c -> is_digit_char c = true.
Proof.
  destruct l as [| a l]; simpl; [discriminate |]; intros H E; injection E as <-.
  apply andb_prop in H; tauto.
Qed.

(* A nonempty string of digits, after an optional minus sign, is read as the
   number it spells. *)
Lemma read_decimal_uint (neg : bool) d : d <> Decimal.Nil ->
  exists q, read_decimal ((if neg then ["-"%char] else []) ++ list_ascii_of_string (NilEmpty.string_of_uint d)) = Some q /\
            Q2R q = (if neg then -1 else 1) * IZR (Z.of_N (Pos.of_uint d)).
Proof.
  intros Hd; unfold read_decimal.
  assert (Hl := uint_chars_digits d).
  destruct (list_ascii_of_string (NilEmpty.string_of_uint d)) as [| c l] eqn:E.
  { destruct d; try discriminate E; contradiction. }
  replace (read_sign ((if neg then ["-"%char] else []) ++ c :: l))
    with (if neg then (-1)%Z else 1%Z, c :: l)
    by (destruct neg; [reflexivity | simpl in Hl; apply andb_prop in Hl as [Hc _];
                                     cbn [app]; now rewrite read_sign_digit]).
  rewrite <- E, read_digits_uint.
  replace (0 + digits_length d)%nat with (S (pred (digits_length d)))
    by (destruct d; simpl; try contradiction; lia).
  simpl; rewrite digits_value_of_uint.
  eexists; split; [reflexivity |].
  unfold Q2R; simpl; destruct neg, (Z.of_N (Pos.of_uint d)); simpl;
    rewrite ?Pos.mul_1_r, ?IZR_NEG; field.
Qed.

Lemma string_of_uint_nonnil d : d <> Decimal.Nil -> NilZero.string_of_uint d = NilEmpty.string_of_uint d.
Proof. destruct d; [contradiction | reflexivity ..]. Qed.

Lemma uint_chars_nonempty d : d <> Decimal.Nil -> list_ascii_of_string (NilEmpty.string_of_uint d) <> [].
Proof. destruct d; [contradiction | discriminate ..]. Qed.

Lemma hd_rev_digit l c : forallb is_digit_char l = true -> hd_error (rev l) = Some c -> c <> " "%char.
Proof. intros H Hc; apply (digit_not_space c), (hd_digit (rev l)); [rewrite forallb_rev |]; assumption. Qed.

(* The literal of an integer k, as the operations table spells it, reads as k. *)
Lemma real_lit_int k : real_lit (NilZero.string_of_int (Z.to_int k)) = Some (IZR k).
Proof.
  destruct k as [| p | p].
  - rewrite (real_lit_Q _ 0%Q) by reflexivity; f_equal; unfold Q2R; simpl; field.
  - assert (Hp := to_uint_nonnil p); assert (Hl := uint_chars_digits (Pos.to_uint p)).
    assert (Hne := uint_chars_nonempty _ Hp).
    unfold real_lit, read_literal; simpl Z.to_int; unfold NilZero.string_of_int.
    rewrite string_of_uint_nonnil by exact Hp.
    rewrite split_digits by exact Hl.
    rewrite strip_id; [| intros c Hc; exact (digit_not_space c (hd_digit _ c Hl Hc)) | intros c Hc; exact (hd_rev_digit _ c Hl Hc)].
    destruct (read_decimal_uint false _ Hp) as [q [Hq HQ]]; simpl app in Hq; rewrite Hq.
    rewrite HQ, Unsigned.of_to; simpl; f_equal; ring.
  - assert (Hp := to_uint_nonnil p); assert (Hl := uint_chars_digits (Pos.to_uint p)).
    assert (Hne := uint_chars_nonempty _ Hp).
    unfold real_lit, read_literal; simpl Z.to_int; unfold NilZero.string_of_int.
    rewrite string_of_uint_nonnil by exact Hp.
    cbn [list_ascii_of_string].
    rewrite split_digits by exact Hl.
    rewrite strip_id; [| intros c Hc; injection Hc as <-; discriminate |].
    + destruct (read_decimal_uint true _ Hp) as [q [Hq HQ]]; simpl app in Hq; rewrite Hq.
      rewrite HQ, Unsigned.of_to; simpl; f_equal; change (Z.neg p) with (- Z.pos p)%Z; rewrite opp_IZR; ring.
    + intros c Hc; simpl in Hc.
      destruct (rev (list_ascii_of_string (NilEmpty.string_of_uint (Pos.to_uint p)))) as [| a r] eqn:Er.
      * apply (f_equal (@rev _)) in Er; rewrite rev_involutive in Er; contradiction.
      * simpl in Hc; injection Hc as <-; apply (hd_rev_digit _ _ Hl); rewrite Er; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   Evaluation across domains. A map g between the numbers of two domains
   extends to the values (`val_map g`). When the operations of the two
   domains commute with g, so do the evaluations: `eval_forward` (when the
   first succeeds, so does the second) and `eval_reflect` (the converse).
   The two terms are two instances of the same program, related by
   term_equiv, with variables paired by g. *)

Definition val_map {A B : Type} (g : A -> B) (v : val A) : val B :=
  match v with
  | VReal x => VReal (g x)
  | VInt k => VInt k
  | VBool b => VBool b
  | VArray l => VArray (map g l)
  | VTape l => VTape (map g l)
  end.

Lemma val_map_compose {A B C : Type} (g1 : A -> B) (g2 : B -> C) v :
  val_map g2 (val_map g1 v) = val_map (fun x => g2 (g1 x)) v.
Proof. destruct v; simpl; rewrite ?map_map; reflexivity. Qed.

Lemma val_map_ext {A B : Type} (g1 g2 : A -> B) v :
  (forall x, g1 x = g2 x) -> val_map g1 v = val_map g2 v.
Proof. intros H; destruct v; simpl; f_equal; try apply H; apply map_ext, H. Qed.

Lemma val_map_id {A : Type} (v : val A) : val_map (fun x => x) v = v.
Proof. destruct v; simpl; rewrite ?map_id; reflexivity. Qed.

(* The pairs of a context related by g. *)
Definition graph {A B : Type} (g : A -> B) (G : list (val A * val B)) : Prop :=
  forall x1 x2, In (x1, x2) G -> x2 = val_map g x1.

Lemma graph_cons {A B : Type} (g : A -> B) G x :
  graph g G -> graph g ((x, val_map g x) :: G).
Proof. intros HG x1 x2 [E | H]; [injection E as -> ->; reflexivity | exact (HG _ _ H)]. Qed.

Lemma nth_z_map {A B : Type} (g : A -> B) k l :
  nth_z k (map g l) = option_map g (nth_z k l).
Proof.
  unfold nth_z; destruct (k <? 0)%Z; [reflexivity |].
  revert l; induction (Z.to_nat k) as [| n IH]; intros [| a l]; simpl; auto.
Qed.

Lemma replace_nth_z_map {A B : Type} (g : A -> B) k x l :
  replace_nth_z k (g x) (map g l) = option_map (map g) (replace_nth_z k x l).
Proof.
  unfold replace_nth_z; destruct (k <? 0)%Z; [reflexivity |].
  revert l; induction (Z.to_nat k) as [| n IH]; intros [| a l]; simpl; auto.
  rewrite IH; destruct (replace_nth n x l); reflexivity.
Qed.

Lemma nth_z_in {A : Type} k (l : list A) x : nth_z k l = Some x -> In x l.
Proof. unfold nth_z; destruct (k <? 0)%Z; [discriminate |]; apply nth_error_In. Qed.

Lemma replace_nth_z_forall {A : Type} (P : A -> Prop) k x l l1 :
  replace_nth_z k x l = Some l1 -> Forall P l -> P x -> Forall P l1.
Proof.
  unfold replace_nth_z; destruct (k <? 0)%Z; [discriminate |].
  revert l l1; induction (Z.to_nat k) as [| n IH]; intros [| a l] l1 H Hl Hx; simpl in H; try discriminate.
  - injection H as <-; inversion Hl; constructor; assumption.
  - destruct (replace_nth n x l) eqn:E; [| discriminate]; injection H as <-.
    inversion Hl; constructor; eauto.
Qed.

(* Inverting val_map. *)
Lemma val_map_inv_real {A B : Type} (g : A -> B) v y :
  val_map g v = VReal y -> exists x, v = VReal x /\ g x = y.
Proof. destruct v; simpl; intros H; inversion H; eauto. Qed.

Lemma val_map_inv_int {A B : Type} (g : A -> B) v k : val_map g v = VInt k -> v = VInt k.
Proof. destruct v; simpl; intros H; inversion H; auto. Qed.

Lemma val_map_inv_bool {A B : Type} (g : A -> B) v b : val_map g v = VBool b -> v = VBool b.
Proof. destruct v; simpl; intros H; inversion H; auto. Qed.

Lemma val_map_inv_array {A B : Type} (g : A -> B) v l :
  val_map g v = VArray l -> exists l1, v = VArray l1 /\ map g l1 = l.
Proof. destruct v; simpl; intros H; inversion H; eauto. Qed.

Lemma int_op2_map {A B : Type} (g : A -> B) f x y :
  val_map g (int_op2 f x y) = int_op2 f x y.
Proof. destruct f; reflexivity. Qed.

(* Unfolds the evaluation of the source, hypothesis by hypothesis. *)
Ltac inv_some :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H as H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : match ?e with _ => _ end = Some _ |- _ => destruct e eqn:?
  end.

Section Forward.
Variables (N1 N2 : Type) (D1 : domain N1) (D2 : domain N2) (g : N1 -> N2).
Hypothesis Hlit : forall s a, dom_lit D1 s = Some a -> dom_lit D2 s = Some (g a).
Hypothesis Hop1 : forall f a b, dom_op1 D1 f a = Some b -> dom_op1 D2 f (g a) = Some (g b).
Hypothesis Hop2 : forall f a b c, dom_op2 D1 f a b = Some c -> dom_op2 D2 f (g a) (g b) = Some (g c).
Hypothesis Hcmp : forall f a b c, dom_cmp D1 f a b = Some c -> dom_cmp D2 f (g a) (g b) = Some c.

Lemma eval_op1_forward f a b :
  eval_op1 D1 f a = Some b -> eval_op1 D2 f (val_map g a) = Some (val_map g b).
Proof.
  destruct a; simpl; try discriminate.
  destruct (dom_op1 D1 f x) eqn:E; intros H; inv_some; rewrite (Hop1 _ _ _ E); reflexivity.
Qed.

Lemma eval_op2_forward f a b c :
  eval_op2 D1 f a b = Some c -> eval_op2 D2 f (val_map g a) (val_map g b) = Some (val_map g c).
Proof.
  destruct a, b; simpl; try discriminate.
  - destruct (comparison f).
    + destruct (dom_cmp D1 f x x0) eqn:E; intros H; inv_some; rewrite (Hcmp _ _ _ _ E); reflexivity.
    + destruct (dom_op2 D1 f x x0) eqn:E; intros H; inv_some; rewrite (Hop2 _ _ _ _ E); reflexivity.
  - intros H; inv_some; rewrite int_op2_map; reflexivity.
Qed.

Lemma eval_map_forward (ev1 : val N1 -> option (val N1)) (ev2 : val N2 -> option (val N2)) :
  (forall w v, ev1 w = Some v -> ev2 (val_map g w) = Some (val_map g v)) ->
  forall n i xs, eval_map ev1 i n = Some xs -> eval_map ev2 i n = Some (map g xs).
Proof.
  intros Hev n; induction n as [| n IH]; intros i xs H; simpl in *; [now inv_some |].
  destruct (ev1 (VInt i)) as [[x | | | |] |] eqn:E1; try discriminate.
  destruct (eval_map ev1 (i + 1)%Z n) eqn:E2; inv_some.
  apply Hev in E1; simpl in E1; rewrite E1, (IH _ _ E2); reflexivity.
Qed.

Lemma eval_fold_forward (ev1 : val N1 -> val N1 -> option (val N1))
  (ev2 : val N2 -> val N2 -> option (val N2)) :
  (forall w s v, ev1 w s = Some v -> ev2 (val_map g w) (val_map g s) = Some (val_map g v)) ->
  forall n i s v, eval_fold ev1 i n s = Some v -> eval_fold ev2 i n (val_map g s) = Some (val_map g v).
Proof.
  intros Hev n; induction n as [| n IH]; intros i s v H; simpl in *; inv_some; [reflexivity |].
  apply Hev in Heqo; simpl in Heqo; rewrite Heqo; exact (IH _ _ _ H).
Qed.

(* When the first evaluation succeeds, the second succeeds, with the image of
   its value: by induction on the relation between the two instances. *)
Lemma eval_forward G t1 t2 :
  term_equiv _ _ G t1 t2 -> graph g G ->
  forall v, eval D1 t1 = Some v -> eval D2 t2 = Some (val_map g v).
Proof.
  induction 1 as [G x1 x2 Hin | G s | G n | G f a1 a2 Ha IHa
                 | G f a1 a2 b1 b2 Ha IHa Hb IHb | G a1 a2 i1 i2 Ha IHa Hi IHi
                 | G a1 a2 i1 i2 v1 v2 Ha IHa Hi IHi Hv IHv
                 | G e1 e2 b1 b2 He IHe Hb IHb
                 | G c1 c2 t1 t2 e1 e2 Hc IHc Ht IHt He IHe
                 | G lo1 lo2 hi1 hi2 b1 b2 Hlo IHlo Hhi IHhi Hb IHb
                 | G lo1 lo2 hi1 hi2 init1 init2 b1 b2 Hlo IHlo Hhi IHhi Hinit IHinit Hb IHb];
    intros HG v Hev; simpl in Hev |- *; inv_some.
  - (* Var *) rewrite (HG _ _ Hin); reflexivity.
  - (* Num *) rewrite (Hlit _ _ Heqo); reflexivity.
  - (* Nat *) reflexivity.
  - (* Op1 *) rewrite (IHa HG _ eq_refl); exact (eval_op1_forward _ _ _ Hev).
  - (* Op2 *) rewrite (IHa HG _ eq_refl), (IHb HG _ eq_refl); exact (eval_op2_forward _ _ _ _ Hev).
  - (* Get *) rewrite (IHa HG _ eq_refl), (IHi HG _ eq_refl); simpl.
    rewrite nth_z_map, Heqo1; reflexivity.
  - (* Set *) rewrite (IHa HG _ eq_refl), (IHi HG _ eq_refl), (IHv HG _ eq_refl); simpl.
    rewrite replace_nth_z_map, Heqo2; reflexivity.
  - (* Let *) rewrite (IHe HG _ eq_refl).
    exact (IHb _ _ (graph_cons _ _ _ HG) _ Hev).
  - (* Ite, then *) rewrite (IHc HG _ eq_refl); exact (IHt HG _ Hev).
  - (* Ite, else *) rewrite (IHc HG _ eq_refl); exact (IHe HG _ Hev).
  - (* Map *) rewrite (IHlo HG _ eq_refl), (IHhi HG _ eq_refl); simpl.
    erewrite eval_map_forward; [reflexivity | | exact Heqo1].
    intros w x Hw; exact (IHb _ _ (graph_cons _ _ _ HG) _ Hw).
  - (* Fold *) rewrite (IHlo HG _ eq_refl), (IHhi HG _ eq_refl), (IHinit HG _ eq_refl).
    apply (eval_fold_forward (fun w s => eval D1 (b1 w s))); [| exact Hev].
    intros w s x Hw; exact (IHb _ _ _ _ (graph_cons _ _ _ (graph_cons _ _ _ HG)) _ Hw).
Qed.

Lemma eval_definition_forward G d1 d2 :
  definition_equiv _ _ G d1 d2 -> graph g G ->
  forall args v, eval_definition D1 d1 args = Some v ->
  eval_definition D2 d2 (map (val_map g) args) = Some (val_map g v).
Proof.
  induction 1 as [G n t r f1 f2 Hf IHf | G r1 r2 b1 b2 Hr Hb]; intros HG args v Hev.
  - destruct args as [| a args]; [discriminate |]; simpl in *.
    exact (IHf _ _ (graph_cons _ _ _ HG) _ _ Hev).
  - destruct args; [| discriminate]; simpl in *.
    exact (eval_forward _ _ _ Hb HG _ Hev).
Qed.

End Forward.

Section Reflect.
Variables (N1 N2 : Type) (D1 : domain N1) (D2 : domain N2) (g : N1 -> N2).
Hypothesis Rlit : forall s b, dom_lit D2 s = Some b -> exists a, dom_lit D1 s = Some a /\ g a = b.
Hypothesis Rop1 : forall f a b, dom_op1 D2 f (g a) = Some b ->
  exists a', dom_op1 D1 f a = Some a' /\ g a' = b.
Hypothesis Rop2 : forall f a b c, dom_op2 D2 f (g a) (g b) = Some c ->
  exists c', dom_op2 D1 f a b = Some c' /\ g c' = c.
Hypothesis Rcmp : forall f a b c, dom_cmp D2 f (g a) (g b) = Some c -> dom_cmp D1 f a b = Some c.

Lemma eval_op1_reflect f a b :
  eval_op1 D2 f (val_map g a) = Some b -> exists b1, eval_op1 D1 f a = Some b1 /\ val_map g b1 = b.
Proof.
  destruct a; simpl; try discriminate.
  destruct (dom_op1 D2 f (g x)) eqn:E; intros H; inv_some.
  destruct (Rop1 _ _ _ E) as [a' [-> <-]]; eexists; split; reflexivity.
Qed.

Lemma eval_op2_reflect f a b c :
  eval_op2 D2 f (val_map g a) (val_map g b) = Some c ->
  exists c1, eval_op2 D1 f a b = Some c1 /\ val_map g c1 = c.
Proof.
  destruct a, b; simpl; try discriminate.
  - destruct (comparison f).
    + destruct (dom_cmp D2 f (g x) (g x0)) eqn:E; intros H; inv_some.
      rewrite (Rcmp _ _ _ _ E); eexists; split; reflexivity.
    + destruct (dom_op2 D2 f (g x) (g x0)) eqn:E; intros H; inv_some.
      destruct (Rop2 _ _ _ _ E) as [c' [-> <-]]; eexists; split; reflexivity.
  - intros H; inv_some; eexists; split; [reflexivity | apply int_op2_map].
Qed.

Lemma eval_map_reflect (ev1 : val N1 -> option (val N1)) (ev2 : val N2 -> option (val N2)) :
  (forall w v, ev2 (val_map g w) = Some v -> exists v1, ev1 w = Some v1 /\ val_map g v1 = v) ->
  forall n i xs, eval_map ev2 i n = Some xs -> exists xs1, eval_map ev1 i n = Some xs1 /\ map g xs1 = xs.
Proof.
  intros Hev n; induction n as [| n IH]; intros i xs H; simpl in *; [inv_some; exists []; auto |].
  destruct (ev2 (VInt i)) as [[x | | | |] |] eqn:E0; try discriminate.
  destruct (eval_map ev2 (i + 1)%Z n) eqn:E3; inv_some.
  destruct (Hev (VInt i) _ E0) as [v1 [E1 M1]]; destruct (val_map_inv_real _ _ _ M1) as [x1 [-> <-]].
  destruct (IH _ _ E3) as [xs1 [E2 <-]].
  exists (x1 :: xs1); simpl; rewrite E1, E2; auto.
Qed.

Lemma eval_fold_reflect (ev1 : val N1 -> val N1 -> option (val N1))
  (ev2 : val N2 -> val N2 -> option (val N2)) :
  (forall w s v, ev2 (val_map g w) (val_map g s) = Some v ->
                 exists v1, ev1 w s = Some v1 /\ val_map g v1 = v) ->
  forall n i s v, eval_fold ev2 i n (val_map g s) = Some v ->
  exists v1, eval_fold ev1 i n s = Some v1 /\ val_map g v1 = v.
Proof.
  intros Hev n; induction n as [| n IH]; intros i s v H; simpl in *; inv_some; [eauto |].
  destruct (Hev (VInt i) _ _ Heqo) as [v1 [E1 <-]].
  rewrite E1; exact (IH _ _ _ H).
Qed.

(* When the second evaluation succeeds, the first succeeds, with a value
   whose image is the value of the second. *)
Lemma eval_reflect G t1 t2 :
  term_equiv _ _ G t1 t2 -> graph g G ->
  forall v, eval D2 t2 = Some v -> exists v1, eval D1 t1 = Some v1 /\ val_map g v1 = v.
Proof.
  induction 1 as [G x1 x2 Hin | G s | G n | G f a1 a2 Ha IHa
                 | G f a1 a2 b1 b2 Ha IHa Hb IHb | G a1 a2 i1 i2 Ha IHa Hi IHi
                 | G a1 a2 i1 i2 v1 v2 Ha IHa Hi IHi Hv IHv
                 | G e1 e2 b1 b2 He IHe Hb IHb
                 | G c1 c2 t1 t2 e1 e2 Hc IHc Ht IHt He IHe
                 | G lo1 lo2 hi1 hi2 b1 b2 Hlo IHlo Hhi IHhi Hb IHb
                 | G lo1 lo2 hi1 hi2 init1 init2 b1 b2 Hlo IHlo Hhi IHhi Hinit IHinit Hb IHb];
    intros HG v Hev; simpl in Hev |- *; inv_some.
  - (* Var *) rewrite (HG _ _ Hin); eauto.
  - (* Num *) destruct (Rlit _ _ Heqo) as [a [-> <-]]; eauto.
  - (* Nat *) eauto.
  - (* Op1 *) destruct (IHa HG _ eq_refl) as [va [-> <-]]; exact (eval_op1_reflect _ _ _ Hev).
  - (* Op2 *) destruct (IHa HG _ eq_refl) as [va [-> <-]]; destruct (IHb HG _ eq_refl) as [vb [-> <-]].
    exact (eval_op2_reflect _ _ _ _ Hev).
  - (* Get *) destruct (IHa HG _ eq_refl) as [va [-> Ma]]; destruct (IHi HG _ eq_refl) as [vi [-> Mi]].
    destruct (val_map_inv_array _ _ _ Ma) as [l1 [-> <-]]; rewrite (val_map_inv_int _ _ _ Mi).
    rewrite nth_z_map in Heqo1; destruct (nth_z k l1) eqn:E; simpl in Heqo1; inv_some; eauto.
  - (* Set *) destruct (IHa HG _ eq_refl) as [va [-> Ma]]; destruct (IHi HG _ eq_refl) as [vi [-> Mi]].
    destruct (IHv HG _ eq_refl) as [vv [-> Mv]].
    destruct (val_map_inv_array _ _ _ Ma) as [l1 [-> <-]]; rewrite (val_map_inv_int _ _ _ Mi).
    destruct (val_map_inv_real _ _ _ Mv) as [x1 [-> <-]].
    rewrite replace_nth_z_map in Heqo2; destruct (replace_nth_z k x1 l1) eqn:E; simpl in Heqo2; inv_some; eauto.
  - (* Let *) destruct (IHe HG _ eq_refl) as [ve [-> <-]].
    exact (IHb _ _ (graph_cons _ _ _ HG) _ Hev).
  - (* Ite, then *) destruct (IHc HG _ eq_refl) as [vc [-> Mc]]; rewrite (val_map_inv_bool _ _ _ Mc).
    exact (IHt HG _ Hev).
  - (* Ite, else *) destruct (IHc HG _ eq_refl) as [vc [-> Mc]]; rewrite (val_map_inv_bool _ _ _ Mc).
    exact (IHe HG _ Hev).
  - (* Map *) destruct (IHlo HG _ eq_refl) as [vl [-> Ml]]; destruct (IHhi HG _ eq_refl) as [vh [-> Mh]].
    rewrite (val_map_inv_int _ _ _ Ml), (val_map_inv_int _ _ _ Mh).
    assert (Hbody : forall w x, eval D2 (b2 (val_map g w)) = Some x ->
                                exists x1, eval D1 (b1 w) = Some x1 /\ val_map g x1 = x)
      by (intros w x Hw; exact (IHb _ _ (graph_cons _ _ _ HG) _ Hw)).
    destruct (eval_map_reflect (fun w => eval D1 (b1 w)) (fun w => eval D2 (b2 w)) Hbody _ _ _ Heqo1)
      as [xs1 [-> <-]]; eauto.
  - (* Fold *) destruct (IHlo HG _ eq_refl) as [vl [-> Ml]]; destruct (IHhi HG _ eq_refl) as [vh [-> Mh]].
    destruct (IHinit HG _ eq_refl) as [vs [-> <-]].
    rewrite (val_map_inv_int _ _ _ Ml), (val_map_inv_int _ _ _ Mh).
    apply (eval_fold_reflect (fun w s => eval D1 (b1 w s)) (fun w s => eval D2 (b2 w s))); [| exact Hev].
    intros w s x Hw; exact (IHb _ _ _ _ (graph_cons _ _ _ (graph_cons _ _ _ HG)) _ Hw).
Qed.

Lemma eval_definition_reflect G d1 d2 :
  definition_equiv _ _ G d1 d2 -> graph g G ->
  forall args v, eval_definition D2 d2 (map (val_map g) args) = Some v ->
  exists v1, eval_definition D1 d1 args = Some v1 /\ val_map g v1 = v.
Proof.
  induction 1 as [G n t r f1 f2 Hf IHf | G r1 r2 b1 b2 Hr Hb]; intros HG args v Hev.
  - destruct args as [| a args]; [discriminate |]; simpl in *.
    exact (IHf _ _ (graph_cons _ _ _ HG) _ _ Hev).
  - destruct args; [| discriminate]; simpl in *.
    exact (eval_reflect _ _ _ Hb HG _ Hev).
Qed.

End Reflect.

(* Inverting term_equiv, constructor by constructor: the right instance has
   the same constructor, with related subterms. *)
Section EquivInversion.
Variables (V1 V2 : Type) (G : list (V1 * V2)).

Lemma equiv_var x1 t2 : term_equiv _ _ G (Var x1) t2 -> exists x2, t2 = Var x2 /\ In (x1, x2) G.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma equiv_num s t2 : term_equiv _ _ G (Num s) t2 -> t2 = Num s.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma equiv_nat k t2 : term_equiv _ _ G (Nat k) t2 -> t2 = Nat k.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma equiv_op1 f a1 t2 : term_equiv _ _ G (Op1 f a1) t2 ->
  exists a2, t2 = Op1 f a2 /\ term_equiv _ _ G a1 a2.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma equiv_op2 f a1 b1 t2 : term_equiv _ _ G (Op2 f a1 b1) t2 ->
  exists a2 b2, t2 = Op2 f a2 b2 /\ term_equiv _ _ G a1 a2 /\ term_equiv _ _ G b1 b2.
Proof. intros H; inversion H; subst; eauto 6. Qed.

Lemma equiv_get a1 i1 t2 : term_equiv _ _ G (Get a1 i1) t2 ->
  exists a2 i2, t2 = Get a2 i2 /\ term_equiv _ _ G a1 a2 /\ term_equiv _ _ G i1 i2.
Proof. intros H; inversion H; subst; eauto 6. Qed.

Lemma equiv_set a1 i1 w1 t2 : term_equiv _ _ G (Set_ a1 i1 w1) t2 ->
  exists a2 i2 w2, t2 = Set_ a2 i2 w2 /\ term_equiv _ _ G a1 a2 /\ term_equiv _ _ G i1 i2
                   /\ term_equiv _ _ G w1 w2.
Proof. intros H; inversion H; subst; eauto 8. Qed.

Lemma equiv_let e1 b1 t2 : term_equiv _ _ G (Let_ e1 b1) t2 ->
  exists e2 b2, t2 = Let_ e2 b2 /\ term_equiv _ _ G e1 e2 /\
    forall x1 x2, term_equiv _ _ ((x1, x2) :: G) (b1 x1) (b2 x2).
Proof. intros H; inversion H; subst; eauto 6. Qed.

Lemma equiv_ite c1 u1 e1 t2 : term_equiv _ _ G (Ite c1 u1 e1) t2 ->
  exists c2 u2 e2, t2 = Ite c2 u2 e2 /\ term_equiv _ _ G c1 c2 /\ term_equiv _ _ G u1 u2
                   /\ term_equiv _ _ G e1 e2.
Proof. intros H; inversion H; subst; eauto 8. Qed.

Lemma equiv_map lo1 hi1 b1 t2 : term_equiv _ _ G (Map lo1 hi1 b1) t2 ->
  exists lo2 hi2 b2, t2 = Map lo2 hi2 b2 /\ term_equiv _ _ G lo1 lo2 /\ term_equiv _ _ G hi1 hi2
    /\ forall x1 x2, term_equiv _ _ ((x1, x2) :: G) (b1 x1) (b2 x2).
Proof. intros H; inversion H; subst; eauto 8. Qed.

Lemma equiv_fold lo1 hi1 init1 b1 t2 : term_equiv _ _ G (Fold lo1 hi1 init1 b1) t2 ->
  exists lo2 hi2 init2 b2, t2 = Fold lo2 hi2 init2 b2 /\ term_equiv _ _ G lo1 lo2
    /\ term_equiv _ _ G hi1 hi2 /\ term_equiv _ _ G init1 init2
    /\ forall i1 i2 s1 s2, term_equiv _ _ ((s1, s2) :: (i1, i2) :: G) (b1 i1 s1) (b2 i2 s2).
Proof. intros H; inversion H; subst; eauto 10. Qed.

End EquivInversion.

(* ---------------------------------------------------------------------------
   The operations, their derivatives, and the tangents of the dual numbers. *)

(* The operations of the reals as total functions (they are total on the
   operators the domains know). *)
Definition real_fun1 (f : unary) (x : R) : R :=
  match real_op1 f x with Some y => y | None => 0 end.

Definition real_fun2 (f : binary) (x y : R) : R :=
  match real_op2 f x y with Some z => z | None => 0 end.

(* The tangents the dual numbers compute. *)
Definition dual_tan1 (f : unary) (x dx : R) : R :=
  match dual_op1 R reals f (Dual x dx) with Some (Dual _ d) => d | None => 0 end.

Definition dual_tan2 (f : binary) (x dx y dy : R) : R :=
  match dual_op2 R reals f (Dual x dx) (Dual y dy) with Some (Dual _ d) => d | None => 0 end.

(* The derivative of a unary operation. *)
Definition derivative1 (f : unary) (x : R) : R :=
  match f with
  | Neg => -1
  | Sin => cos x
  | Cos => - sin x
  | Exp => exp x
  | Log => / x
  | Sqrt => / (2 * sqrt x)
  | Pow k => IZR k * powerRZ x (k - 1)
  | Unknown1 _ => 0
  end.

(* Where smooth_reals computes, it computes as the reals. *)
Lemma smooth_op1_real f x y : smooth_op1 f x = Some y -> real_op1 f x = Some y.
Proof.
  destruct f; simpl; auto; try (destruct (Rle_dec x 0); [discriminate | auto]).
  destruct (k <? 0)%Z; auto; destruct (Req_dec_T x 0); [discriminate | auto].
Qed.

Lemma smooth_op2_real f x y z : smooth_op2 f x y = Some z -> real_op2 f x y = Some z.
Proof. destruct f; simpl; auto; destruct (Req_dec_T y 0); [discriminate | auto]. Qed.

Lemma smooth_cmp_real f x y c : smooth_cmp f x y = Some c -> real_cmp f x y = Some c.
Proof. unfold smooth_cmp; destruct (Req_dec_T x y); [discriminate | auto]. Qed.

Lemma smooth_op1_fun f x y : smooth_op1 f x = Some y -> y = real_fun1 f x.
Proof. intros H; unfold real_fun1; rewrite (smooth_op1_real _ _ _ H); reflexivity. Qed.

Lemma smooth_op2_fun f x y z : smooth_op2 f x y = Some z -> z = real_fun2 f x y.
Proof. intros H; unfold real_fun2; rewrite (smooth_op2_real _ _ _ _ H); reflexivity. Qed.

(* Where an operation is defined (smooth_reals), the dual numbers compute its
   value and its derivative times the tangent. *)
Lemma dual_op1_spec f x dx y : smooth_op1 f x = Some y ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y (dual_tan1 f x dx)) /\
  dual_tan1 f x dx = derivative1 f x * dx.
Proof.
  intros H; assert (Hr := smooth_op1_real _ _ _ H).
  unfold dual_tan1, dual_op1; change (dom_op1 reals f x) with (real_op1 f x); rewrite Hr.
  destruct f; try discriminate Hr; cbn [real_op1] in Hr; injection Hr as <-;
    cbn [dual_partial1 dom_lit dom_op1 dom_op2 reals real_op1 real_op2 derivative1];
    rewrite ?real_lit_m1, ?real_lit_1, ?real_lit_2; try (split; [reflexivity | ring]).
  - (* Log *) split; [reflexivity |]; simpl in H; destruct (Rle_dec x 0); [discriminate |]; field; lra.
  - (* Sqrt *) split; [reflexivity |]; simpl in H; destruct (Rle_dec x 0); [discriminate |].
    assert (0 < sqrt x) by (apply sqrt_lt_R0; lra); field; lra.
  - (* Pow *) destruct k as [| p | p].
    + rewrite real_lit_0; split; [reflexivity | simpl; ring].
    + rewrite (real_lit_int (Z.pos p)); split; [reflexivity | ring].
    + rewrite (real_lit_int (Z.neg p)); split; [reflexivity | ring].
Qed.

(* The derivative of x |-> x^k is k x^(k-1), at x <> 0 when k < 0: from that
   of x |-> x^n, composed with the inverse for a negative exponent. *)
Lemma is_derive_powerRZ k x : (0 <= k)%Z \/ x <> 0 ->
  is_derive (fun y => powerRZ y k) x (IZR k * powerRZ x (k - 1)).
Proof.
  intros Hk; destruct k as [| p | p].
  - apply is_derive_Reals; replace (IZR 0 * powerRZ x (0 - 1)) with 0 by ring.
    exact (derivable_pt_lim_const 1 x).
  - apply is_derive_Reals.
    replace (IZR (Z.pos p) * powerRZ x (Z.pos p - 1)) with (INR (Pos.to_nat p) * x ^ Init.Nat.pred (Pos.to_nat p)).
    + apply derivable_pt_lim_pow.
    + rewrite INR_IZR_INZ, positive_nat_Z; f_equal.
      assert (Hn := Pos2Nat.is_pos p).
      replace (Z.pos p - 1)%Z with (Z.of_nat (Init.Nat.pred (Pos.to_nat p))) by lia.
      apply pow_powerRZ.
  - destruct Hk as [Hk | Hx]; [lia |].
    assert (Hn := Pos2Nat.is_pos p).
    apply is_derive_Reals.
    replace (IZR (Z.neg p) * powerRZ x (Z.neg p - 1))
      with (- (INR (Pos.to_nat p) * x ^ Init.Nat.pred (Pos.to_nat p)) / (x ^ Pos.to_nat p) ^ 2).
    + apply is_derive_Reals, (is_derive_inv (fun y => y ^ Pos.to_nat p)).
      * apply is_derive_Reals, derivable_pt_lim_pow.
      * apply pow_nonzero, Hx.
    + replace (Z.neg p - 1)%Z with (Z.neg (Pos.succ p)) by lia; simpl.
      rewrite Pos2Nat.inj_succ.
      change (IZR (Z.neg p)) with (- IZR (Z.pos p)).
      replace (IZR (Z.pos p)) with (INR (Pos.to_nat p)) by (rewrite INR_IZR_INZ, positive_nat_Z; reflexivity).
      destruct (Pos.to_nat p) as [| m]; [lia |]; rewrite S_INR; simpl.
      assert (x ^ m <> 0) by (apply pow_nonzero, Hx).
      field; split; auto.
Qed.

(* Where an operation is defined (smooth_reals), it is differentiable, with
   the derivative `derivative1`: the derivatives of the Stdlib. *)
Lemma is_derive_op1 f x y : smooth_op1 f x = Some y -> is_derive (real_fun1 f) x (derivative1 f x).
Proof.
  intros H; apply is_derive_Reals; destruct f; simpl in H.
  - replace (derivative1 Neg x) with (- 1) by (simpl; ring).
    exact (derivable_pt_lim_opp id x 1 (derivable_pt_lim_id x)).
  - exact (derivable_pt_lim_sin x).
  - exact (derivable_pt_lim_cos x).
  - exact (derivable_pt_lim_exp x).
  - destruct (Rle_dec x 0); [discriminate |]; apply derivable_pt_lim_ln; lra.
  - destruct (Rle_dec x 0); [discriminate |]; apply derivable_pt_lim_sqrt; lra.
  - apply is_derive_Reals, is_derive_powerRZ.
    destruct (k <? 0)%Z eqn:Ek; [| left; apply Z.ltb_ge, Ek].
    destruct (Req_dec_T x 0); [discriminate | right; assumption].
  - discriminate.
Qed.

(* Where a binary operation is defined, the dual numbers compute its value
   and the tangent of Domain.v. *)
Lemma dual_op2_spec f x dx y dy z : smooth_op2 f x y = Some z ->
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z (dual_tan2 f x dx y dy)).
Proof.
  intros H; apply smooth_op2_real in H.
  unfold dual_tan2; destruct f; simpl in H |- *; try discriminate H; injection H as <-; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   The domain of families. Around a point e0 of a normed module E, a number
   is a function r : E -> R with a derivative dr : E -> R. A literal is a
   constant; an operation composes, with the derivative of the dual numbers
   (`dual_tan1`, `dual_tan2`), and fails where smooth_reals fails at e0; a
   comparison compares at e0, as smooth_reals. *)

Section Families.
Context {E : NormedModule R_AbsRing} (e0 : E).

Local Notation fam := ((E -> R) * (E -> R))%type.

(* A family is good when it is differentiable at e0 with its derivative. *)
Definition good (p : fam) : Prop := filterdiff (fst p) (locally e0) (snd p).

Definition good_val (v : val fam) : Prop :=
  match v with
  | VReal p => good p
  | VArray l | VTape l => Forall good l
  | VInt _ | VBool _ => True
  end.

Definition fam_lit (s : string) : option fam :=
  match real_lit s, real_lit "0" with
  | Some c, Some z => Some (fun _ => c, fun _ => z)
  | _, _ => None
  end.

Definition fam_op1 (f : unary) (p : fam) : option fam :=
  match smooth_op1 f (fst p e0) with
  | Some _ => Some (fun y => real_fun1 f (fst p y), fun h => dual_tan1 f (fst p e0) (snd p h))
  | None => None
  end.

Definition fam_op2 (f : binary) (p q : fam) : option fam :=
  match smooth_op2 f (fst p e0) (fst q e0) with
  | Some _ => Some (fun y => real_fun2 f (fst p y) (fst q y),
                    fun h => dual_tan2 f (fst p e0) (snd p h) (fst q e0) (snd q h))
  | None => None
  end.

Definition fam_cmp (f : binary) (p q : fam) : option bool := smooth_cmp f (fst p e0) (fst q e0).

Definition families : domain fam := Domain fam_lit fam_op1 fam_op2 fam_cmp.

(* A family at a point, and as a dual number at e0 in the direction h. *)
Definition at_point (y : E) (p : fam) : R := fst p y.
Definition dual_at (h : E) (p : fam) : dual R := Dual (fst p e0) (snd p h).

(* --- the families at e0 are the smooth reals --- *)

Lemma families_reflect_lit s b :
  dom_lit smooth_reals s = Some b -> exists a, dom_lit families s = Some a /\ at_point e0 a = b.
Proof. simpl; unfold fam_lit; rewrite real_lit_0; intros ->; eexists; split; reflexivity. Qed.

Lemma families_reflect_op1 f a b :
  dom_op1 smooth_reals f (at_point e0 a) = Some b ->
  exists a', dom_op1 families f a = Some a' /\ at_point e0 a' = b.
Proof.
  simpl; unfold fam_op1, at_point; intros H; rewrite H; eexists; split; [reflexivity |].
  symmetry; exact (smooth_op1_fun _ _ _ H).
Qed.

Lemma families_reflect_op2 f a b c :
  dom_op2 smooth_reals f (at_point e0 a) (at_point e0 b) = Some c ->
  exists c', dom_op2 families f a b = Some c' /\ at_point e0 c' = c.
Proof.
  simpl; unfold fam_op2, at_point; intros H; rewrite H; eexists; split; [reflexivity |].
  symmetry; exact (smooth_op2_fun _ _ _ _ H).
Qed.

Lemma families_reflect_cmp f a b c :
  dom_cmp smooth_reals f (at_point e0 a) (at_point e0 b) = Some c -> dom_cmp families f a b = Some c.
Proof. exact (fun H => H). Qed.

(* --- the dual numbers compute the families at e0, with their derivatives --- *)

Lemma families_dual_lit h s a :
  dom_lit families s = Some a -> dom_lit (duals reals) s = Some (dual_at h a).
Proof.
  simpl; unfold fam_lit, dual_lit; simpl.
  destruct (real_lit s), (real_lit "0"); intros H; inv_some; reflexivity.
Qed.

Lemma families_dual_op1 h f a b :
  dom_op1 families f a = Some b -> dom_op1 (duals reals) f (dual_at h a) = Some (dual_at h b).
Proof.
  cbn [dom_op1 families]; unfold fam_op1, dual_at.
  destruct (smooth_op1 f (fst a e0)) eqn:Es; intros H; inv_some.
  cbn [dom_op1 duals fst snd]; rewrite (proj1 (dual_op1_spec _ _ (snd a h) _ Es)).
  rewrite <- (smooth_op1_fun _ _ _ Es); reflexivity.
Qed.

Lemma families_dual_op2 h f a b c :
  dom_op2 families f a b = Some c -> dom_op2 (duals reals) f (dual_at h a) (dual_at h b) = Some (dual_at h c).
Proof.
  cbn [dom_op2 families]; unfold fam_op2, dual_at.
  destruct (smooth_op2 f (fst a e0) (fst b e0)) eqn:Es; intros H; inv_some.
  cbn [dom_op2 duals fst snd]; rewrite (dual_op2_spec _ _ (snd a h) _ (snd b h) _ Es).
  rewrite <- (smooth_op2_fun _ _ _ _ Es); reflexivity.
Qed.

Lemma families_dual_cmp h f a b c :
  dom_cmp families f a b = Some c -> dom_cmp (duals reals) f (dual_at h a) (dual_at h b) = Some c.
Proof. simpl; unfold fam_cmp, dual_at; simpl; apply smooth_cmp_real. Qed.

(* --- the families are good --- *)

Lemma good_lit s a : dom_lit families s = Some a -> good a.
Proof.
  simpl; unfold fam_lit; rewrite real_lit_0; destruct (real_lit s); intros H; inv_some.
  unfold good; simpl; apply (filterdiff_ext_lin _ (fun _ => Hierarchy.zero)); [apply filterdiff_const | reflexivity].
Qed.

Lemma good_op1 f a b : good a -> dom_op1 families f a = Some b -> good b.
Proof.
  simpl; unfold fam_op1, good; destruct (smooth_op1 f (fst a e0)) eqn:Es; intros Ha H; inv_some; simpl.
  eapply filterdiff_ext_lin.
  - exact (filterdiff_comp' (fst a) (real_fun1 f) e0 (snd a) _ Ha (is_derive_op1 _ _ _ Es)).
  - intros h; rewrite (proj2 (dual_op1_spec _ _ (snd a h) _ Es)); apply Rmult_comm.
Qed.

Lemma good_op2 f a b c : good a -> good b -> dom_op2 families f a b = Some c -> good c.
Proof.
  simpl; unfold fam_op2, good; destruct (smooth_op2 f (fst a e0) (fst b e0)) eqn:Es; intros Ha Hb H; inv_some.
  destruct f; simpl in Es |- *; try discriminate Es.
  - (* Add *) exact (filterdiff_plus_fct _ _ _ _ Ha Hb).
  - (* Sub *) exact (filterdiff_minus_fct _ _ _ _ Ha Hb).
  - (* Mul *) eapply filterdiff_ext_lin; [exact (filterdiff_mult_fct _ _ e0 _ _ Rmult_comm Ha Hb) |].
    intros h; simpl; unfold dual_tan2; simpl.
    change (snd a h * fst b e0 + fst a e0 * snd b h = fst b e0 * snd a h + fst a e0 * snd b h); ring.
  - (* Divide *) destruct (Req_dec_T (fst b e0) 0) as [| Hy]; [discriminate |].
    assert (Hinv := filterdiff_comp' (fst b) (fun t => / t) e0 (snd b) _ Hb
                      (is_derive_inv (fun t => t) (fst b e0) 1 (is_derive_id _) Hy)).
    eapply filterdiff_ext_lin; [exact (filterdiff_mult_fct _ _ e0 _ _ Rmult_comm Ha Hinv) |].
    intros h; simpl; unfold dual_tan2; simpl.
    change (snd a h * / fst b e0 + fst a e0 * (snd b h * (- (1) / (fst b e0 * (fst b e0 * 1))))
            = (snd a h - fst a e0 / fst b e0 * snd b h) / fst b e0).
    field; exact Hy.
Qed.

(* --- at a point, the reals compute the families --- *)

Lemma point_lit y s a : dom_lit families s = Some a -> real_lit s = Some (at_point y a).
Proof. simpl; unfold fam_lit; destruct (real_lit s), (real_lit "0"); intros H; inv_some; reflexivity. Qed.

Lemma point_op1 y f a b :
  dom_op1 families f a = Some b -> real_op1 f (at_point y a) = Some (at_point y b).
Proof.
  simpl; unfold fam_op1, at_point; destruct (smooth_op1 f (fst a e0)) eqn:Es; intros H; inv_some; simpl.
  unfold real_fun1; destruct f; try discriminate Es; reflexivity.
Qed.

Lemma point_op2 y f a b c :
  dom_op2 families f a b = Some c -> real_op2 f (at_point y a) (at_point y b) = Some (at_point y c).
Proof.
  simpl; unfold fam_op2, at_point; destruct (smooth_op2 f (fst a e0) (fst b e0)) eqn:Es; intros H; inv_some; simpl.
  unfold real_fun2; destruct f; try discriminate Es; reflexivity.
Qed.

(* A differentiable function, positive at e0, is positive around e0. *)
Lemma locally_pos (g dg : E -> R) : filterdiff g (locally e0) dg -> 0 < g e0 ->
  locally e0 (fun y => 0 < g y).
Proof.
  intros Hg Hp; pose proof (filterdiff_continuous g e0 (ex_intro _ dg Hg)) as Hc.
  apply (Hc (fun z => 0 < z)).
  exists (mkposreal _ Hp); intros z Hz.
  unfold ball in Hz; simpl in Hz; unfold AbsRing_ball, abs, minus, plus, opp in Hz; simpl in Hz.
  apply Rabs_def2 in Hz; lra.
Qed.

(* Two good families ordered at e0 stay ordered around e0. *)
Lemma locally_lt a b : good a -> good b -> fst a e0 < fst b e0 ->
  locally e0 (fun y => fst a y < fst b y).
Proof.
  intros Ha Hb Hlt.
  apply (filter_imp (fun y => 0 < minus (fst b y) (fst a y))).
  - intros y H; change (0 < fst b y + - fst a y) in H; lra.
  - apply (locally_pos _ _ (filterdiff_minus_fct _ _ _ _ Hb Ha)).
    change (0 < fst b e0 + - fst a e0); lra.
Qed.

(* Decides the tests of real comparisons in the goal. *)
Ltac decide_ifs :=
  repeat match goal with |- context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
  try reflexivity; lra.

Lemma real_cmp_lt f x y x' y' : x < y -> x' < y' -> real_cmp f x y = real_cmp f x' y'.
Proof.
  intros H H'; destruct f; simpl; try reflexivity; decide_ifs.
Qed.

(* A comparison of good families, decided at e0 (no tie), is decided the same
   way around e0. *)
Lemma point_cmp f a b c : good a -> good b -> dom_cmp families f a b = Some c ->
  locally e0 (fun y => real_cmp f (at_point y a) (at_point y b) = Some c).
Proof.
  simpl; unfold fam_cmp, smooth_cmp, at_point; intros Ha Hb.
  destruct (Req_dec_T (fst a e0) (fst b e0)) as [| Hne]; [discriminate |]; intros Hc.
  destruct (Rlt_dec (fst a e0) (fst b e0)) as [Hlt | Hge].
  - apply (filter_imp _ _ (fun y Hy => eq_trans (real_cmp_lt f _ _ _ _ Hy Hlt) Hc)).
    exact (locally_lt _ _ Ha Hb Hlt).
  - assert (Hgt : fst b e0 < fst a e0) by lra.
    apply (filter_imp (fun y => fst b y < fst a y)); [| exact (locally_lt _ _ Hb Ha Hgt)].
    intros y Hy; rewrite <- Hc; destruct f; simpl; try reflexivity; decide_ifs.
Qed.

(* --- the evaluation at the points around e0 --- *)

(* The context relating the family instance to the instance at the point y. *)
Definition ctx_at (y : E) (G : list (val fam)) : list (val fam * val R) :=
  map (fun v => (v, val_map (at_point y) v)) G.

Lemma in_ctx_at y G x1 x2 : In (x1, x2) (ctx_at y G) -> In x1 G /\ x2 = val_map (at_point y) x1.
Proof. unfold ctx_at; rewrite in_map_iff; intros [v [E1 Hv]]; injection E1 as -> ->; auto. Qed.

(* What the evaluation of a term over the families says about the points
   around e0: its value is good, and around e0 the evaluation over the reals
   of the instance at y computes the value at y. The existence of an
   instance related at e0 says that the term is closed in G. *)
Definition near_ok (t1 : term (val fam)) : Prop :=
  forall G v1, Forall good_val G ->
  (exists t2, term_equiv _ _ (ctx_at e0 G) t1 t2) ->
  eval families t1 = Some v1 ->
  good_val v1 /\
  locally e0 (fun y => forall t2, term_equiv _ _ (ctx_at y G) t1 t2 ->
                                  eval reals t2 = Some (val_map (at_point y) v1)).

Lemma eval_map_near (b : val fam -> term (val fam)) G :
  (forall x, near_ok (b x)) -> Forall good_val G ->
  (exists b2, forall x1 x2, term_equiv _ _ ((x1, x2) :: ctx_at e0 G) (b x1) (b2 x2)) ->
  forall n i xs, eval_map (fun v => eval families (b v)) i n = Some xs ->
  Forall good xs /\
  locally e0 (fun y => forall b2, (forall x1 x2, term_equiv _ _ ((x1, x2) :: ctx_at y G) (b x1) (b2 x2)) ->
              eval_map (fun v => eval reals (b2 v)) i n = Some (map (at_point y) xs)).
Proof.
  intros Hb HG [b0 Hb0] n; induction n as [| n IH]; intros i xs H; simpl in H.
  - inv_some; split; [constructor | apply filter_forall; reflexivity].
  - destruct (eval families (b (VInt i))) as [[x | | | |] |] eqn:E1; try discriminate.
    destruct (eval_map (fun v => eval families (b v)) (i + 1)%Z n) as [xs' |] eqn:E2; inv_some.
    destruct (Hb (VInt i) (VInt i :: G) _ (Forall_cons (VInt i) (I : good_val (VInt i)) HG) (ex_intro _ _ (Hb0 _ _)) E1) as [Hx Hnear].
    destruct (IH _ _ E2) as [Hxs Hnear'].
    split; [constructor; assumption |].
    eapply filter_imp; [| exact (filter_and _ _ Hnear Hnear')]; intros y [Hy Hy'] b2 Hb2; simpl.
    specialize (Hy _ (Hb2 (VInt i) (VInt i))); simpl in Hy; rewrite Hy, (Hy' _ Hb2); reflexivity.
Qed.

Lemma eval_fold_near (b : val fam -> val fam -> term (val fam)) G :
  (forall x s, near_ok (b x s)) -> Forall good_val G ->
  (exists b2, forall i1 i2 s1 s2, term_equiv _ _ ((s1, s2) :: (i1, i2) :: ctx_at e0 G) (b i1 s1) (b2 i2 s2)) ->
  forall n i s v, good_val s -> eval_fold (fun w x => eval families (b w x)) i n s = Some v ->
  good_val v /\
  locally e0 (fun y => forall b2,
    (forall i1 i2 s1 s2, term_equiv _ _ ((s1, s2) :: (i1, i2) :: ctx_at y G) (b i1 s1) (b2 i2 s2)) ->
    eval_fold (fun w x => eval reals (b2 w x)) i n (val_map (at_point y) s) = Some (val_map (at_point y) v)).
Proof.
  intros Hb HG [b0 Hb0] n; induction n as [| n IH]; intros i s v Hs H; simpl in H.
  - inv_some; split; [assumption | apply filter_forall; reflexivity].
  - destruct (eval families (b (VInt i) s)) as [s1 |] eqn:E1; [| discriminate].
    destruct (Hb (VInt i) s (s :: VInt i :: G) _ (Forall_cons _ Hs (Forall_cons (VInt i) (I : good_val (VInt i)) HG))
                (ex_intro _ _ (Hb0 _ _ _ _)) E1) as [Hs1 Hnear].
    destruct (IH _ _ _ Hs1 H) as [Hv Hnear'].
    split; [assumption |].
    eapply filter_imp; [| exact (filter_and _ _ Hnear Hnear')]; intros y [Hy Hy'] b2 Hb2; simpl.
    specialize (Hy _ (Hb2 (VInt i) (VInt i) s _)); simpl in Hy; rewrite Hy; exact (Hy' _ Hb2).
Qed.

(* The evaluation over the families says it all about the points around e0:
   by induction on the term, at the family instance. *)
Lemma eval_near t1 : near_ok t1.
Proof.
  induction t1 as [x | s | k | f a IHa | f a IHa b IHb | a IHa i IHi | a IHa i IHi w IHw
                  | e IHe b IHb | c IHc t IHt e IHe | lo IHlo hi IHhi b IHb
                  | lo IHlo hi IHhi init IHinit b IHb];
    intros G v1 HG [t0 Ht0] Hev; simpl in Hev.
  - (* Var *) inv_some.
    destruct (equiv_var _ _ _ _ _ Ht0) as [x2 [-> Hin]].
    destruct (in_ctx_at _ _ _ _ Hin) as [Hx _]; split; [exact (proj1 (Forall_forall _ _) HG _ Hx) |].
    apply filter_forall; intros y t2 Ht2; destruct (equiv_var _ _ _ _ _ Ht2) as [x3 [-> Hin3]].
    destruct (in_ctx_at _ _ _ _ Hin3) as [_ ->]; reflexivity.
  - (* Num *) destruct (fam_lit s) as [p |] eqn:Es; inv_some; split; [exact (good_lit _ _ Es) |].
    apply filter_forall; intros y t2 Ht2; rewrite (equiv_num _ _ _ _ _ Ht2); simpl.
    rewrite (point_lit y _ _ Es); reflexivity.
  - (* Nat *) inv_some; split; [exact I |].
    apply filter_forall; intros y t2 Ht2; rewrite (equiv_nat _ _ _ _ _ Ht2); reflexivity.
  - (* Op1 *) destruct (eval families a) as [va |] eqn:Ea; [| discriminate].
    destruct (equiv_op1 _ _ _ _ _ _ Ht0) as [a0 [_ Ha0]].
    destruct (IHa G va HG (ex_intro _ _ Ha0) Ea) as [Hga Hnear].
    destruct va as [p | | | |]; try discriminate; simpl in Hev.
    destruct (fam_op1 f p) as [q |] eqn:Eq; inv_some; split; [exact (good_op1 _ _ _ Hga Eq) |].
    eapply filter_imp; [| exact Hnear]; intros y Hy t2 Ht2.
    destruct (equiv_op1 _ _ _ _ _ _ Ht2) as [a2 [-> Ha2]]; simpl; rewrite (Hy _ Ha2); simpl.
    rewrite (point_op1 y _ _ _ Eq); reflexivity.
  - (* Op2 *) destruct (eval families a) as [va |] eqn:Ea; [| discriminate].
    destruct (eval families b) as [vb |] eqn:Eb; [| discriminate].
    destruct (equiv_op2 _ _ _ _ _ _ _ Ht0) as [a0 [b0 [_ [Ha0 Hb0]]]].
    destruct (IHa G va HG (ex_intro _ _ Ha0) Ea) as [Hga Hna].
    destruct (IHb G vb HG (ex_intro _ _ Hb0) Eb) as [Hgb Hnb].
    assert (Hboth : locally e0 (fun y => forall a2 b2, term_equiv _ _ (ctx_at y G) a a2 ->
                      term_equiv _ _ (ctx_at y G) b b2 ->
                      eval reals (Op2 f a2 b2) = eval_op2 reals f (val_map (at_point y) va) (val_map (at_point y) vb))).
    { eapply filter_imp; [| exact (filter_and _ _ Hna Hnb)]; intros y [Hy Hy'] a2 b2 Ha2 Hb2.
      simpl; rewrite (Hy _ Ha2), (Hy' _ Hb2); reflexivity. }
    destruct va as [p | ka | | |], vb as [q | kb | | |]; simpl in Hev; try discriminate.
    + destruct (comparison f) eqn:Ecmp.
      * destruct (fam_cmp f p q) as [cb |] eqn:Ec; inv_some; split; [exact I |].
        eapply filter_imp; [| exact (filter_and _ _ Hboth (point_cmp _ _ _ _ Hga Hgb Ec))].
        intros y [Hy Hc] t2 Ht2; destruct (equiv_op2 _ _ _ _ _ _ _ Ht2) as [a2 [b2 [-> [Ha2 Hb2]]]].
        rewrite (Hy _ _ Ha2 Hb2); simpl; rewrite Ecmp; simpl; rewrite Hc; reflexivity.
      * destruct (fam_op2 f p q) as [r |] eqn:Eo; inv_some.
        split; [exact (good_op2 _ _ _ _ Hga Hgb Eo) |].
        eapply filter_imp; [| exact Hboth].
        intros y Hy t2 Ht2; destruct (equiv_op2 _ _ _ _ _ _ _ Ht2) as [a2 [b2 [-> [Ha2 Hb2]]]].
        rewrite (Hy _ _ Ha2 Hb2); simpl; rewrite Ecmp; simpl.
        rewrite (point_op2 y _ _ _ _ Eo); reflexivity.
    + inv_some; split; [destruct f; exact I |].
      eapply filter_imp; [| exact Hboth].
      intros y Hy t2 Ht2; destruct (equiv_op2 _ _ _ _ _ _ _ Ht2) as [a2 [b2 [-> [Ha2 Hb2]]]].
      rewrite (Hy _ _ Ha2 Hb2), int_op2_map; reflexivity.
  - (* Get *) destruct (equiv_get _ _ _ _ _ _ Ht0) as [a0 [i0 [_ [Ha0 Hi0]]]].
    destruct (eval families a) as [va |] eqn:Ea; [| discriminate].
    destruct (eval families i) as [vi |] eqn:Ei; [| destruct va; discriminate].
    destruct (IHa G va HG (ex_intro _ _ Ha0) Ea) as [Hga Hna].
    destruct (IHi G vi HG (ex_intro _ _ Hi0) Ei) as [_ Hni].
    destruct va as [| | | l |]; try discriminate; destruct vi as [| k | | |]; try discriminate.
    destruct (nth_z k l) as [p |] eqn:En; inv_some.
    split; [exact (proj1 (Forall_forall _ _) Hga _ (nth_z_in _ _ _ En)) |].
    eapply filter_imp; [| exact (filter_and _ _ Hna Hni)]; intros y [Hy Hy'] t2 Ht2.
    destruct (equiv_get _ _ _ _ _ _ Ht2) as [a2 [i2 [-> [Ha2 Hi2]]]].
    simpl; rewrite (Hy _ Ha2), (Hy' _ Hi2); simpl; rewrite nth_z_map, En; reflexivity.
  - (* Set *) destruct (equiv_set _ _ _ _ _ _ _ Ht0) as [a0 [i0 [w0 [_ [Ha0 [Hi0 Hw0]]]]]].
    destruct (eval families a) as [va |] eqn:Ea; [| discriminate].
    destruct (eval families i) as [vi |] eqn:Ei; [| destruct va; discriminate].
    destruct (eval families w) as [vw |] eqn:Ew; [| destruct va, vi; discriminate].
    destruct (IHa G va HG (ex_intro _ _ Ha0) Ea) as [Hga Hna].
    destruct (IHi G vi HG (ex_intro _ _ Hi0) Ei) as [_ Hni].
    destruct (IHw G vw HG (ex_intro _ _ Hw0) Ew) as [Hgw Hnw].
    destruct va as [| | | l |]; try discriminate; destruct vi as [| k | | |]; try discriminate.
    destruct vw as [p | | | |]; try discriminate.
    destruct (replace_nth_z k p l) as [l1 |] eqn:En; inv_some.
    split; [exact (replace_nth_z_forall _ _ _ _ _ En Hga Hgw) |].
    eapply filter_imp; [| exact (filter_and _ _ Hna (filter_and _ _ Hni Hnw))].
    intros y [Hy [Hy' Hy'']] t2 Ht2.
    destruct (equiv_set _ _ _ _ _ _ _ Ht2) as [a2 [i2 [w2 [-> [Ha2 [Hi2 Hw2]]]]]].
    simpl; rewrite (Hy _ Ha2), (Hy' _ Hi2), (Hy'' _ Hw2); simpl.
    rewrite (replace_nth_z_map (at_point y)), En; reflexivity.
  - (* Let *) destruct (equiv_let _ _ _ _ _ _ Ht0) as [e0' [b0 [_ [He0 Hb0]]]].
    destruct (eval families e) as [ve |] eqn:Ee; [| discriminate].
    destruct (IHe G ve HG (ex_intro _ _ He0) Ee) as [Hge Hne].
    destruct (IHb ve (ve :: G) v1 (Forall_cons _ Hge HG) (ex_intro _ _ (Hb0 _ _)) Hev) as [Hgv Hnb].
    split; [exact Hgv |].
    eapply filter_imp; [| exact (filter_and _ _ Hne Hnb)]; intros y [Hy Hy'] t2 Ht2.
    destruct (equiv_let _ _ _ _ _ _ Ht2) as [e2 [b2 [-> [He2 Hb2]]]].
    simpl; rewrite (Hy _ He2); exact (Hy' _ (Hb2 _ _)).
  - (* Ite *) destruct (equiv_ite _ _ _ _ _ _ _ Ht0) as [c0 [t0' [e0' [_ [Hc0 [Ht0' He0]]]]]].
    destruct (eval families c) as [vc |] eqn:Ec; [| discriminate].
    destruct (IHc G vc HG (ex_intro _ _ Hc0) Ec) as [_ Hnc].
    destruct vc as [| | [] | |]; try discriminate.
    + destruct (IHt G v1 HG (ex_intro _ _ Ht0') Hev) as [Hgv Hnt]; split; [exact Hgv |].
      eapply filter_imp; [| exact (filter_and _ _ Hnc Hnt)]; intros y [Hy Hy'] t2 Ht2.
      destruct (equiv_ite _ _ _ _ _ _ _ Ht2) as [c2 [t2' [e2 [-> [Hc2 [Ht2' He2]]]]]].
      simpl; rewrite (Hy _ Hc2); exact (Hy' _ Ht2').
    + destruct (IHe G v1 HG (ex_intro _ _ He0) Hev) as [Hgv Hne]; split; [exact Hgv |].
      eapply filter_imp; [| exact (filter_and _ _ Hnc Hne)]; intros y [Hy Hy'] t2 Ht2.
      destruct (equiv_ite _ _ _ _ _ _ _ Ht2) as [c2 [t2' [e2 [-> [Hc2 [Ht2' He2]]]]]].
      simpl; rewrite (Hy _ Hc2); exact (Hy' _ He2).
  - (* Map *) destruct (equiv_map _ _ _ _ _ _ _ Ht0) as [lo0 [hi0 [b0 [_ [Hlo0 [Hhi0 Hb0]]]]]].
    destruct (eval families lo) as [vl |] eqn:El; [| discriminate].
    destruct (eval families hi) as [vh |] eqn:Eh; [| destruct vl; discriminate].
    destruct (IHlo G vl HG (ex_intro _ _ Hlo0) El) as [_ Hnl].
    destruct (IHhi G vh HG (ex_intro _ _ Hhi0) Eh) as [_ Hnh].
    destruct vl as [| i | | |]; try discriminate; destruct vh as [| j | | |]; try discriminate.
    destruct (eval_map (fun v => eval families (b v)) i (count i j)) as [xs |] eqn:Em; inv_some.
    destruct (eval_map_near b G IHb HG (ex_intro _ _ Hb0) _ _ _ Em) as [Hxs Hnm].
    split; [exact Hxs |].
    eapply filter_imp; [| exact (filter_and _ _ Hnl (filter_and _ _ Hnh Hnm))].
    intros y [Hy [Hy' Hy'']] t2 Ht2.
    destruct (equiv_map _ _ _ _ _ _ _ Ht2) as [lo2 [hi2 [b2 [-> [Hlo2 [Hhi2 Hb2]]]]]].
    simpl; rewrite (Hy _ Hlo2), (Hy' _ Hhi2); simpl; rewrite (Hy'' _ Hb2); reflexivity.
  - (* Fold *) destruct (equiv_fold _ _ _ _ _ _ _ _ Ht0) as [lo0 [hi0 [init0 [b0 [_ [Hlo0 [Hhi0 [Hinit0 Hb0]]]]]]]].
    destruct (eval families lo) as [vl |] eqn:El; [| discriminate].
    destruct (eval families hi) as [vh |] eqn:Eh; [| destruct vl; discriminate].
    destruct (eval families init) as [vs |] eqn:Es; [| destruct vl, vh; discriminate].
    destruct (IHlo G vl HG (ex_intro _ _ Hlo0) El) as [_ Hnl].
    destruct (IHhi G vh HG (ex_intro _ _ Hhi0) Eh) as [_ Hnh].
    destruct (IHinit G vs HG (ex_intro _ _ Hinit0) Es) as [Hgs Hns].
    destruct vl as [| i | | |]; try discriminate; destruct vh as [| j | | |]; try discriminate.
    destruct (eval_fold_near b G IHb HG (ex_intro _ _ Hb0) _ _ _ _ Hgs Hev) as [Hgv Hnf].
    split; [exact Hgv |].
    eapply filter_imp; [| exact (filter_and _ _ Hnl (filter_and _ _ Hnh (filter_and _ _ Hns Hnf)))].
    intros y [Hy [Hy' [Hy'' Hy''']]] t2 Ht2.
    destruct (equiv_fold _ _ _ _ _ _ _ _ Ht2) as [lo2 [hi2 [init2 [b2 [-> [Hlo2 [Hhi2 [Hinit2 Hb2]]]]]]]].
    simpl; rewrite (Hy _ Hlo2), (Hy' _ Hhi2), (Hy'' _ Hinit2); simpl; exact (Hy''' _ Hb2).
Qed.

(* The same for a function: its arguments opened one by one. *)
Lemma eval_definition_near d1 : forall G args v1,
  Forall good_val G -> Forall good_val args ->
  (exists d2, definition_equiv _ _ (ctx_at e0 G) d1 d2) ->
  eval_definition families d1 args = Some v1 ->
  good_val v1 /\
  locally e0 (fun y => forall d2, definition_equiv _ _ (ctx_at y G) d1 d2 ->
    eval_definition reals d2 (map (val_map (at_point y)) args) = Some (val_map (at_point y) v1)).
Proof.
  induction d1 as [n t r f IHf | r b]; intros G args v1 HG Hargs [d0 Hd0] Hev.
  - destruct args as [| a args]; [discriminate |]; simpl in Hev.
    inversion Hargs as [| ? ? Ha Hargs']; subst.
    inversion Hd0 as [? ? ? ? ? Hf0 |]; subst.
    destruct (IHf a (a :: G) args v1 (Forall_cons _ Ha HG) Hargs' (ex_intro _ _ (Hf0 _ _)) Hev)
      as [Hgv Hnear].
    split; [exact Hgv |].
    eapply filter_imp; [| exact Hnear]; intros y Hy d2 Hd2.
    inversion Hd2 as [? ? ? ? ? Hf2 |]; subst; simpl; exact (Hy _ (Hf2 _ _)).
  - destruct args; [| discriminate]; simpl in Hev.
    inversion Hd0 as [| ? ? ? b0 Hr0 Hb0]; subst.
    destruct (eval_near b G v1 HG (ex_intro _ _ Hb0) Hev) as [Hgv Hnear].
    split; [exact Hgv |].
    eapply filter_imp; [| exact Hnear]; intros y Hy d2 Hd2.
    inversion Hd2 as [| ? ? ? b2 Hr2 Hb2]; subst; simpl; exact (Hy _ Hb2).
Qed.

End Families.

(* ---------------------------------------------------------------------------
   The layout of the arguments. The real coordinates of a list of arguments
   are its reals and the elements of its arrays, in order; the integers, the
   booleans and the tapes are not differentiated. `lay real other x j` maps
   each real coordinate of x, numbered from j, by `real`, and each element of
   a tape by `other`. *)

Definition reals_of_val (v : val R) : list R :=
  match v with VReal r => [r] | VArray l => l | _ => [] end.

Definition reals_of_args (x : list (val R)) : list R := concat (map reals_of_val x).

Fixpoint lay_list {A : Type} (real : nat -> R -> A) (l : list R) (j : nat) : list A :=
  match l with
  | [] => []
  | r :: l' => real j r :: lay_list real l' (S j)
  end.

Fixpoint lay {A : Type} (real : nat -> R -> A) (other : R -> A) (x : list (val R)) (j : nat)
  : list (val A) :=
  match x with
  | [] => []
  | VReal r :: x' => VReal (real j r) :: lay real other x' (S j)
  | VArray l :: x' => VArray (lay_list real l j) :: lay real other x' (j + length l)
  | VInt k :: x' => VInt k :: lay real other x' j
  | VBool b :: x' => VBool b :: lay real other x' j
  | VTape l :: x' => VTape (map other l) :: lay real other x' j
  end.

(* The arguments x with their reals replaced by those of r, in order. *)
Definition with_reals (x : list (val R)) (r : list R) : list (val R) :=
  lay (fun j _ => nth j r 0) (fun r => r) x 0.

Definition in_dim (x : list (val R)) : nat := length (reals_of_args x).

(* The number of reals of the value of f at x. *)
Definition out_dim (f : function) (x : list (val R)) : nat :=
  match eval_function reals f x with Some v => length (reals_of_val v) | None => 0 end.

(* f as a function of the reals of its arguments: from R^n to R^m. *)
Definition value_of (f : function) (x : list (val R)) (y : Rn (in_dim x)) : Rn (out_dim f x) :=
  vec_of_list (out_dim f x)
    (match eval_function reals f (with_reals x (list_of_vec (in_dim x) y)) with
     | Some v => reals_of_val v
     | None => []
     end).

(* The arguments x as dual numbers, each real with the tangent of dx at its
   position. *)
Definition dual_args (x : list (val R)) (dx : list R) : list (val (dual R)) :=
  lay (fun j r => Dual r (nth j dx 0)) (fun r => Dual r 0) x 0.

Definition primal_val (v : val (dual R)) : val R := val_map (fun d => let 'Dual a _ := d in a) v.

Definition tangent_reals (v : val (dual R)) : list R :=
  match v with
  | VReal (Dual _ d) => [d]
  | VArray l => map (fun d => let 'Dual _ t := d in t) l
  | _ => []
  end.

Lemma lay_list_map {A B : Type} (g : A -> B) real l j :
  map g (lay_list real l j) = lay_list (fun j r => g (real j r)) l j.
Proof. revert j; induction l; intros j; simpl; f_equal; auto. Qed.

Lemma lay_map {A B : Type} (g : A -> B) real other x j :
  map (val_map g) (lay real other x j) = lay (fun j r => g (real j r)) (fun r => g (other r)) x j.
Proof.
  revert j; induction x as [| [] x IH]; intros j; simpl; rewrite ?IH, ?lay_list_map, ?map_map; reflexivity.
Qed.

Lemma lay_list_ext {A : Type} (real1 real2 : nat -> R -> A) l j :
  (forall j r, real1 j r = real2 j r) -> lay_list real1 l j = lay_list real2 l j.
Proof. intros H; revert j; induction l; intros j; simpl; f_equal; auto. Qed.

Lemma lay_ext {A : Type} (real1 real2 : nat -> R -> A) other1 other2 x j :
  (forall j r, real1 j r = real2 j r) -> (forall r, other1 r = other2 r) ->
  lay real1 other1 x j = lay real2 other2 x j.
Proof.
  intros H1 H2; revert j; induction x as [| [] x IH]; intros j; simpl; rewrite ?IH, ?H1; try reflexivity.
  - rewrite (lay_list_ext _ _ _ _ H1); reflexivity.
  - rewrite (map_ext _ _ H2); reflexivity.
Qed.

(* A function of the position that reads the coordinate at that position is
   a function of the coordinate. *)
Lemma lay_list_nth {A : Type} (real : nat -> R -> A) pre l rest :
  lay_list (fun j _ => real j (nth j (pre ++ l ++ rest) 0)) l (length pre) = lay_list real l (length pre).
Proof.
  revert pre; induction l as [| r l IH]; intros pre; simpl; [reflexivity |].
  rewrite nth_middle; f_equal.
  replace (S (length pre)) with (length (app pre [r])) by (rewrite length_app; simpl; lia).
  rewrite <- (IH (app pre [r])), <- app_assoc; reflexivity.
Qed.

Lemma lay_nth {A : Type} (real : nat -> R -> A) other pre x :
  lay (fun j _ => real j (nth j (pre ++ reals_of_args x) 0)) other x (length pre)
  = lay real other x (length pre).
Proof.
  revert pre; induction x as [| v x IH]; intros pre; [reflexivity |].
  unfold reals_of_args; simpl; fold (reals_of_args x).
  destruct v as [r | k | b | l | l]; simpl.
  - rewrite nth_middle; f_equal.
    replace (S (length pre)) with (length (app pre [r])) by (rewrite length_app; simpl; lia).
    rewrite <- (IH (app pre [r])), <- app_assoc; reflexivity.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - f_equal; [f_equal; apply lay_list_nth |].
    replace (length pre + length l)%nat with (length (app pre l)) by apply length_app.
    rewrite <- (IH (app pre l)), <- app_assoc; reflexivity.
  - f_equal; apply IH.
Qed.

Lemma lay_list_id l j : lay_list (fun _ r => r) l j = l.
Proof. revert j; induction l; intros j; simpl; f_equal; auto. Qed.

(* Laying out x with the identity gives x. *)
Lemma lay_id x j : lay (fun _ r => r) (fun r => r) x j = x.
Proof.
  revert j; induction x as [| [] x IH]; intros j; simpl; rewrite ?IH, ?map_id, ?lay_list_id; reflexivity.
Qed.

(* The reals of x put back into x give x. *)
Lemma with_reals_id x : with_reals x (reals_of_args x) = x.
Proof.
  unfold with_reals; rewrite (lay_nth (fun _ r => r) _ [] x); apply lay_id.
Qed.

(* The real coordinates of a value, in any domain: those of reals_of_val. *)
Definition val_reals {A : Type} (v : val A) : list A :=
  match v with VReal r => [r] | VArray l => l | _ => [] end.

Lemma reals_of_val_reals v : reals_of_val v = val_reals v.
Proof. destruct v; reflexivity. Qed.

Lemma val_reals_map {A B : Type} (g : A -> B) v : val_reals (val_map g v) = map g (val_reals v).
Proof. destruct v; reflexivity. Qed.

Lemma tangent_reals_map {A : Type} (g : A -> dual R) v :
  tangent_reals (val_map g v) = map (fun a => let 'Dual _ t := g a in t) (val_reals v).
Proof. destruct v as [a | | | |]; simpl; rewrite ?map_map; try reflexivity; destruct (g a); reflexivity. Qed.

(* ---------------------------------------------------------------------------
   The arguments as families on R^n, n = in_dim x: the real coordinate number
   j is the j-th coordinate function, with itself as derivative (it is
   linear); an element of a tape is a constant, with derivative 0. *)

Local Notation famn n := ((Rn n -> R) * (Rn n -> R))%type.

Definition fam_lay (n : nat) (x : list (val R)) (j : nat) : list (val (famn n)) :=
  lay (fun j _ => (coord n j, coord n j)) (fun r => (fun _ => r, fun _ => 0)) x j.

Definition fam_args (x : list (val R)) : list (val (famn (in_dim x))) := fam_lay (in_dim x) x 0.

(* The arguments are good families at every point: a coordinate is linear,
   hence its own derivative; a constant has derivative 0. *)
Lemma fam_lay_good n (e0 : Rn n) x j : Forall (good_val e0) (fam_lay n x j).
Proof.
  unfold fam_lay; revert j; induction x as [| v x IH]; intros j; [constructor |].
  assert (Hc : forall j, good e0 (coord n j, coord n j))
    by (intros k; apply filterdiff_linear, coord_linear).
  destruct v as [r | k | b | l | l]; simpl; constructor; auto; simpl; try apply Hc; try exact I.
  - (* an array: its coordinates *)
    clear IH; revert j; induction l as [| r l IHl]; intros j; simpl; constructor; auto.
  - (* a tape: constants *)
    apply Forall_forall; intros p Hp; apply in_map_iff in Hp as [r [<- _]].
    unfold good; simpl.
    apply (filterdiff_ext_lin _ (fun _ => Hierarchy.zero)); [apply filterdiff_const | reflexivity].
Qed.

(* At a point y of R^n, the arguments are x with its reals replaced by the
   coordinates of y. *)
Lemma fam_args_at x (y : Rn (in_dim x)) :
  map (val_map (at_point y)) (fam_args x) = with_reals x (list_of_vec (in_dim x) y).
Proof.
  unfold fam_args, fam_lay, with_reals; rewrite lay_map.
  apply lay_ext; reflexivity.
Qed.

(* The point of x itself. *)
Definition point_of (x : list (val R)) : Rn (in_dim x) := vec_of_list (in_dim x) (reals_of_args x).

(* At the point of x, the arguments are x. *)
Lemma fam_args_point x : map (val_map (at_point (point_of x))) (fam_args x) = x.
Proof.
  rewrite fam_args_at; unfold point_of; rewrite list_of_vec_of_list by reflexivity.
  apply with_reals_id.
Qed.

(* As dual numbers at the point of x in the direction dx, the arguments are
   the dual arguments seeded with dx. *)
Lemma fam_args_dual x dx : length dx = in_dim x ->
  map (val_map (dual_at (point_of x) (vec_of_list (in_dim x) dx))) (fam_args x) = dual_args x dx.
Proof.
  intros Hdx; unfold fam_args, fam_lay, dual_args; rewrite lay_map.
  etransitivity; [| exact (lay_nth (fun j r => Dual r (nth j dx 0)) (fun r => Dual r 0) [] x)].
  apply lay_ext; [intros j r | reflexivity].
  unfold dual_at, coord, point_of; simpl.
  rewrite !list_of_vec_of_list by auto; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   The theorem. Let f be parametric and defined at x (no tie, no operation
   where it is not differentiable). Then f, as a function of the reals of its
   arguments, is Fréchet-differentiable at x, with a linear derivative df;
   and the dual numbers, seeded with any direction dx, compute the value of f
   at x and df dx.

   Proof: evaluate f over the families of the arguments at the point e0 of
   x. Reflection (from smooth_reals at x) makes this evaluation succeed, with
   a value v1 whose families are good (eval_definition_near) and computed by
   the reals around e0: so value_of f x is, around e0, the vector of the
   functions of v1, differentiable with the vector of their derivatives
   (filterdiff_vec). The dual numbers compute the image of v1 by dual_at
   (eval_definition_forward): its primal part is v1 at e0, the value of f at
   x, and its tangents are the derivatives of v1 applied to dx. *)

Theorem duals_derive (f : function) (x : list (val R)) :
  parametric f -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (vec_of_list (in_dim x) (reals_of_args x))) df /\
    forall dx, length dx = in_dim x ->
      exists vd, eval_function (duals reals) f (dual_args x dx) = Some vd /\
                 primal_val vd = v /\
                 tangent_reals vd = list_of_vec _ (df (vec_of_list _ dx)).
Proof.
  intros Hpar [v Hv].
  change (vec_of_list (in_dim x) (reals_of_args x)) with (point_of x).
  set (e0 := point_of x).
  assert (Hnil : forall A B (g : A -> B), graph g []) by (intros A B g x1 x2 []).
  (* reflection: over the families, f succeeds with a value v1, v at e0 *)
  destruct (eval_definition_reflect _ _ (families e0) smooth_reals (at_point e0)
              (families_reflect_lit e0) (families_reflect_op1 e0) (families_reflect_op2 e0)
              (families_reflect_cmp e0) [] _ _ (Hpar _ _) (Hnil _ _ _) (fam_args x) v)
    as [v1 [Hv1 Hv1e0]].
  { unfold e0; rewrite fam_args_point; exact Hv. }
  (* around e0, v1 is good and computed by the reals *)
  destruct (eval_definition_near e0 (fdef f _) [] (fam_args x) v1 (Forall_nil _)
              (fam_lay_good _ e0 x 0) (ex_intro _ _ (Hpar _ _)) Hv1) as [Hgood Hnear].
  assert (Hreal : locally e0 (fun y =>
            eval_function reals f (with_reals x (list_of_vec (in_dim x) y)) = Some (val_map (at_point y) v1))).
  { eapply filter_imp; [| exact Hnear]; intros y Hy.
    rewrite <- fam_args_at; exact (Hy _ (Hpar _ _)). }
  (* the number of reals of the value *)
  assert (Hout : out_dim f x = length (val_reals v1)).
  { unfold out_dim; pose proof (locally_singleton _ _ Hreal) as H0; simpl in H0.
    unfold e0, point_of in H0; rewrite list_of_vec_of_list, with_reals_id in H0 by reflexivity.
    rewrite H0, reals_of_val_reals, val_reals_map, length_map; reflexivity. }
  assert (Hgoods : List.Forall (fun p => filterdiff (fst p) (locally e0) (snd p)) (val_reals v1))
    by (destruct v1; simpl in Hgood |- *; auto).
  exists v, (fun h => vec_of_list (out_dim f x) (map (fun p => snd p h) (val_reals v1))).
  split; [exact Hv | split].
  - (* differentiable: around e0, value_of is the vector of the families of v1 *)
    apply (filterdiff_ext_locally (fun y => vec_of_list (out_dim f x) (map (fun p => fst p y) (val_reals v1)))).
    + eapply filter_imp; [| exact Hreal]; intros y Hy.
      unfold value_of; rewrite Hy, reals_of_val_reals, val_reals_map; reflexivity.
    + apply filterdiff_vec_length; [symmetry; exact Hout | exact Hgoods].
  - (* the dual numbers compute v1 at e0 and its derivatives in the direction dx *)
    intros dx Hdx.
    set (h := vec_of_list (in_dim x) dx).
    pose proof (eval_definition_forward _ _ (families e0) (duals reals) (dual_at e0 h)
                  (families_dual_lit e0 h) (families_dual_op1 e0 h) (families_dual_op2 e0 h)
                  (families_dual_cmp e0 h) [] _ _ (Hpar _ _) (Hnil _ _ _) _ _ Hv1) as Hd.
    unfold h, e0 in Hd; rewrite fam_args_dual in Hd by exact Hdx.
    eexists; split; [exact Hd | split].
    + unfold primal_val; rewrite val_map_compose, <- Hv1e0; apply val_map_ext; reflexivity.
    + rewrite tangent_reals_map, list_of_vec_of_list by (rewrite length_map; symmetry; exact Hout).
      apply map_ext; reflexivity.
Qed.
