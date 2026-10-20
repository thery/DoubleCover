(* AdjointNBody.v — the bodies of in-place loops of any depth (nbody): a
   prefix of operations and reads, then a set of the state, or an in-place
   fold on the state whose body is again an nbody, or the state itself.

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

(* The body of an in-place loop on the state s: operations and reads, then
   a set ending it, or an in-place fold on s ending it, whose body is again
   such a body on its own state, or the state s itself. *)
Fixpoint nbody (s : pv) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' =>
      match e with
      | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => forall x, nbody s (b' x)
      | ASet _ _ _ => forall x, b' x = ARet (AVar x)
      | AFold _ _ _ (AVar s') bi =>
          s' = s /\ (forall x y, nbody y (bi x y)) /\
          forall x, b' x = ARet (AVar x)
      | _ => False
      end
  | ARet (AVar s') => s' = s
  | ARet _ => False
  end.

(* Whether an analysed body ends with a set. *)
Fixpoint aset_tail (k : nat) (b : anf avar bare) : bool :=
  match b with
  | ALet _ e b' =>
      match e with
      | ASet _ _ _ => true
      | AFold _ _ _ _ _ => false
      | _ => aset_tail (S k) (b' (let_binder k e))
      end
  | ARet _ => false
  end.

Lemma abody_nbody s b : abody b -> nbody s b.
Proof.
elim: b => [a e b' IH | x] //=.
by case: e => // *; auto.
Qed.

(* The operations and reads a body of an in-place loop starts with. *)
Definition is_op {V I : Type} (e : value V I) : Prop :=
  match e with AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True | _ => False end.

(* Induction on the bodies of in-place loops, through the inner folds. *)
Lemma nbody_ind (P : pv -> anf pv bare -> Prop) :
  (forall s a e b', is_op e -> (forall x, nbody s (b' x)) ->
     (forall x, P s (b' x)) -> P s (ALet a e b')) ->
  (forall s a aP iP vP b', (forall x, b' x = ARet (AVar x)) ->
     P s (ALet a (ASet aP iP vP) b')) ->
  (forall s a fa lo hi bi b', (forall x y, nbody y (bi x y)) ->
     (forall x y, P y (bi x y)) -> (forall x, b' x = ARet (AVar x)) ->
     P s (ALet a (AFold fa lo hi (AVar s) bi) b')) ->
  (forall s, P s (ARet (AVar s))) ->
  forall s b, nbody s b -> P s b.
Proof.
move=> Hop Hset Hfold Hret.
have [Hb _] : (forall b, forall s, nbody s b -> P s b) /\
    (forall e : value pv bare, match e with
     | AFold _ _ _ _ bi => forall x y s, nbody s (bi x y) -> P s (bi x y)
     | _ => True end).
  apply: (anf_value_ind pv bare (fun b => forall s, nbody s b -> P s b)
    (fun e => match e with
     | AFold _ _ _ _ bi => forall x y s, nbody s (bi x y) -> P s (bi x y)
     | _ => True end)) => //.
  - move=> a e IHe b' IHb s.
    case: e IHe => //= [f x | f x y | x i | x i y | fa lo hi [s' | ? | ?] bi]
      IHe //= Hn.
    + by apply: Hop => // x0; apply: IHb; exact: Hn.
    + by apply: Hop => // x0; apply: IHb; exact: Hn.
    + by apply: Hop => // x0; apply: IHb; exact: Hn.
    + exact: Hset.
    case: Hn => -> [Hbi Hr].
    by apply: Hfold => // x y; apply: IHe; exact: Hbi.
  - by move=> [x | ? | ?] s //= ->; exact: Hret.
by move=> s b; exact: Hb.
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

Section NBody.
Variable cv : bool.

Lemma nbody_ibody s b : nbody s b -> ibody s b.
Proof.
elim: b s => [a e b' IH | [x | ? | ?]] s //=.
case: e => //; try by move=> *; auto.
by move=> ? ? ? [s' | ? | ?] bi //= [-> [_ Hb]].
Qed.

(* An array is updated in place by a fold on it, a scalar is a fold
   carrying a real. *)
Lemma array_or_not (p : pv) :
  is_array (vty (pw p)) \/ ~ is_array (vty (pw p)).
Proof. by case: (vty (pw p)) => [| | | z] /=; auto. Qed.

(* A body of an in-place loop computes a value of its type, of zero tangent
   when it is not varied. *)
Lemma nbody_act s b : nbody s b -> act_body b.
Proof.
move: s b; apply: nbody_ind.
- move=> s a e b' Hop _ IH; apply: act_let; last exact: IH.
  case: e Hop => //= *; [exact: act_op1 | exact: act_op2 | exact: act_get].
- move=> s a aP iP vP b' Hr; apply: act_let; first exact: act_set.
  by move=> x; rewrite Hr; exact: act_ret.
- move=> s a fa lo hi bi b' _ IH Hr; apply: act_let; last first.
    by move=> x; rewrite Hr; exact: act_ret.
  case: (array_or_not s) => Ha.
    by apply: act_fold_gen => //; exists s.
  by apply: act_fold => // p [<-].
by move=> s; exact: act_ret.
Qed.

(* A body of an in-place loop whose analysed instance ends with a fold
   ends with that fold, in the instance of well_formed too. *)
Lemma nbody_ends GA G k s (bP : anf pv bare) bA bW :
  nbody s bP -> anf_eq GA bP bA -> anf_eq G bP bW ->
  (forall p w, In (p, w) G -> (aid (pa p) < k)%nat) ->
  tail_fold_live cv k bA <> None -> ends_with_fold k bW = true.
Proof.
elim: bP s GA G k bA bW => [a e b' IH | x] s GA G k [aA eA cA | aA]
  [aW eW cW | aW] //=.
move=> Hb [HeA HcA] [HeW HcW] Hlt Htl.
set x := PV (let_binder k eA) (anon k) dummy_tvar (VInt 0%Z) 0.
have Hlt' : forall p w, In (p, w) ((x, anon k) :: G) ->
    (aid (pa p) < S k)%nat.
  by move=> p w [[<- _] | I] /=; [lia | have := Hlt _ _ I; lia].
case: e Hb HeA HeW
  => // [? ? | ? ? ? | ? ? | ? ? ? | a1 lo1 hi1 [s' | ? | ?] bi] //= Hb HeA HeW.
- case: eA HeA Htl x Hlt' => //= ? ? _ Htl x Hlt'.
  case: eW HeW => //= ? ? _.
  exact: (IH x s _ _ (S k) _ _ (Hb x) (HcA x _) (HcW x _) Hlt' Htl).
- case: eA HeA Htl x Hlt' => //= ? ? ? _ Htl x Hlt'.
  case: eW HeW => //= ? ? ? _.
  exact: (IH x s _ _ (S k) _ _ (Hb x) (HcA x _) (HcW x _) Hlt' Htl).
- case: eA HeA Htl x Hlt' => //= ? ? _ Htl x Hlt'.
  case: eW HeW => //= ? ? _.
  exact: (IH x s _ _ (S k) _ _ (Hb x) (HcA x _) (HcW x _) Hlt' Htl).
- case: eA HeA Htl x Hlt' => //= a2 i2 v2 _ Htl x Hlt'.
  exfalso; apply: Htl.
  have := HcA x (let_binder k (ASet a2 i2 v2)); rewrite (Hb x).
  by case: (cA _).
case: Hb => _ [_ Hret].
case: eW HeW => // ? ? ? ? ? _ /=.
have := HcW x (anon k); rewrite Hret /WellFormed.is_tail.
case: (cW (anon k)) => [? ? ? | [v | ? | ?]] //= [Ev | I].
  by case: Ev => <-; rewrite Nat.eqb_refl.
by have := Hlt _ _ I; rewrite /=; lia.
Qed.

(* The replay of a step ending with a fold does not read the state j of
   the loop. *)
Lemma nbody_needs s (bP : anf pv bare) : nbody s bP ->
  forall G G1 bA bW bW1 k j wr ix sv t,
  anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> anf_eq G1 bP bW1 ->
  agree G1 (gW G) k -> (forall q, In q G -> aid (pa q) = vid (pw q)) ->
  (forall p w, In (p, w) G1 -> vid w = j -> vty w <> Integer) ->
  (j < k)%nat -> vid sv = j ->
  typecheck wr (ArrayBody ix (AVar sv)) k bW1 = (t, Ok) ->
  reads_around_inner_loop j k bW = false ->
  tail_fold_live cv k bA <> None ->
  atom_member (AVar (AV j false)) (snd (needs cv Replay k bA)) = false.
Proof.
elim: bP s => [a e b' IH | x] s //= Hb G G1 [aA eA cA | ?] [aW eW cW | ?]
  [aW1 eW1 cW1 | ?] k j wr ix sv t //= [HeA HcA] [HeW HcW] [HeW1 HcW1]
  Hag Hid Hty Hjk Hsv Htc Hra Htl.
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
have Hop : (forall x, nbody s (b' x)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) <> None ->
    occurs_value j k eW = false ->
    reads_around_inner_loop j (S k) (cW (anon k)) = false ->
    atom_member (AVar (AV j false)) (snd (needs cv Replay k
      (ALet aA eA cA))) = false.
  move=> Hb' Htl' Hocc Hra'.
  have IHc := IH x1 s (Hb' x1) (x1 :: G) _ _ _ (cW1 (VInfo k te None)) (S k)
    j wr ix sv t (HcA _ _) (HcW _ _) (HcW1 _ _) Hag' Hid' Hty' HjS Hsv Htc
    Hra' Htl'.
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
have Hnt : tail_fold_live cv (S k) (cA (let_binder k eA)) <> None ->
    WellFormed.is_tail cW k = false.
  move=> Htl'; rewrite /WellFormed.is_tail.
  move: (HcW x1 (anon k)) (HcA x1 (let_binder k eA)) Htl'.
  case: (b' x1) => [? ? ? | ?]; case: (cW (anon k)) => // ? _.
  by case: (cA _) => // ? _ /(_ erefl).
have Hends : (forall x, nbody s (b' x)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) <> None ->
    ends_with_fold (S k) (cW (anon k)) = true.
  move=> Hb' Htl'.
  have Hlt : forall p w, In (p, w) ((x1, anon k) :: gW G) ->
      (aid (pa p) < S k)%nat.
    by case: Hag' => _ Hlt p w I; exact: Hlt _ _ (or_intror I).
  exact: (nbody_ends _ _ _ s (b' x1) _ _ (Hb' x1)
    (HcA x1 (let_binder k eA)) (HcW x1 (anon k)) Hlt Htl').
have Hnf : (forall x, nbody s (b' x)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) <> None ->
    (forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0) ->
    occurs_value j k eW = false /\
    reads_around_inner_loop j (S k) (cW (anon k)) = false.
  move=> Hb' Htl' Hne; move: Hra; rewrite /reads_around_inner_loop.
  have Ee : forall ew, (forall a0 lo0 hi0 i0 bb0,
      ew <> AFold a0 lo0 hi0 i0 bb0) ->
      ends_with_fold k (ALet aW ew cW) = ends_with_fold (S k) (cW (anon k)).
    by case=> //= ? ? ? ? ? /(_ _ _ _ _ _ erefl).
  rewrite (Ee _ Hne).
  rewrite /= Hnt // Hends //= => /orb_false_iff [Ho Hr].
  by rewrite Ho Hr.
have Htlc : (forall a0 lo0 hi0 i0 bb0, eA <> AFold a0 lo0 hi0 i0 bb0) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) <> None.
  move=> Hne; move: Htl => /=.
  case Ee: eA Hne
    => [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? ?] Hne;
    try by rewrite -Ee.
  by case: (Hne _ _ _ _ _ erefl).
case: e Hb HeA HeW HeW1 Hop
  => //= [? ? | ? ? ? | ? ? | ? ? ? | a1 lo hi [s' | ? | ?] bi]
  //= Hb HeA HeW HeW1 Hop.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  have HneA : forall a0 lo0 hi0 i0 bb0, eA <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeA; rewrite E => -[].
  have [Ho Hr] := Hnf Hb (Htlc HneA) Hne.
  exact: Hop Hb (Htlc HneA) Ho Hr.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  have HneA : forall a0 lo0 hi0 i0 bb0, eA <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeA; rewrite E => -[].
  have [Ho Hr] := Hnf Hb (Htlc HneA) Hne.
  exact: Hop Hb (Htlc HneA) Ho Hr.
- have Hne : forall a0 lo0 hi0 i0 bb0, eW <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeW; rewrite E => -[].
  have HneA : forall a0 lo0 hi0 i0 bb0, eA <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeA; rewrite E => -[].
  have [Ho Hr] := Hnf Hb (Htlc HneA) Hne.
  exact: Hop Hb (Htlc HneA) Ho Hr.
- have HneA : forall a0 lo0 hi0 i0 bb0, eA <> AFold a0 lo0 hi0 i0 bb0.
    by move=> ? ? ? ? ? E; move: HeA; rewrite E => -[].
  exfalso; apply: (Htlc HneA).
  by have := HcA x1 (let_binder k eA); rewrite (Hb x1); case: (cA _).
(* the inner fold, the tail *)
case: Hb => _ [_ Hret]; clear Hop Hnf Hnt Hends Htlc Htl.
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

(* The state of a loop whose step ends with an inner fold is not read by
   the reverse loop. *)
Lemma nbody_state_dead L k (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
  (forall x y, nbody y (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  (forall p, In p L -> aid (pa p) = vid (pw p)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) ->
  reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))) =
    false ->
  tail_fold_live cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) <> None ->
  state_live cv k initA bA = false.
Proof.
move=> Hfb HbA HbW Hid Hk HtB Hra Htl.
rewrite /state_live /fold_binders atom_member_id /=.
set vr := fold_varied k initA bA.
set ix := PV (AV k false) (anon k) dummy_tvar (VInt 0%Z) 0.
set sx := PV (AV (S k) vr) (anon (S k)) dummy_tvar (VInt 0%Z) 0.
have Hag : agree (gW L) (gW L) k.
  split; first by move=> p w1 w2 /in_gW [_ ->] /in_gW [_ ->].
  by move=> p w [] /in_gW [I _]; rewrite Hid //; exact: Hk.
apply: (nbody_needs sx (bP ix sx) (Hfb ix sx) (sx :: ix :: L)
  ((sx, VInfo (S k) (Array z) None) :: (ix, VInfo k Integer None) :: gW L)
  _ _ _ (S (S k)) (S k) (option_map (amap pw) wP)
  (AVar (VInfo k Integer None)) (VInfo (S k) (Array z) None) (Array z)
  (HbA ix _ sx _) (HbW ix _ sx _) (HbW ix _ sx _)) => //.
- by apply: agree_cons => //; apply: agree_cons.
- by move=> q [<- | [<- | Hq]] //; exact: Hid.
move=> p w [[_ <-] // | [[_ <-] /= | /in_gW [I ->] E]]; first lia.
by have := Hk _ I; lia.
Qed.

(* A step that gives its state back needs nothing: the result is its
   state, and no let before it is useful. *)
Lemma nbody_ret_needs s (bP : anf pv bare) : nbody s bP ->
  forall L k bA, anf_eq (gA L) bP bA -> (aid (pa s) < k)%nat ->
  aset_tail k bA = false -> tail_fold_live cv k bA = None ->
  needs cv Replay k bA = ([AVar (pa s)], []).
Proof.
elim: bP s => [a e b' IH | x] s Hb L k [aA eA cA | aA] //=; last first.
  move=> /atom_graph [-> _] _ _ _.
  by case: x Hb => //= s' ->.
move=> [HeA HcA] Hk Hset Htl.
set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have Hst : same_term (AVar (let_binder k eA)) (AVar (pa s)) = false.
  by apply/Nat.eqb_neq => /=; lia.
have Hop : (forall y, nbody s (b' y)) ->
    aset_tail (S k) (cA (let_binder k eA)) = false ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) = None ->
    needs cv Replay k (ALet aA eA cA) = ([AVar (pa s)], []).
  move=> Hb' Hs' Ht'.
  have Hk' : (aid (pa s) < S k)%nat by lia.
  have IHc := IH x s (Hb' x) (x :: L) (S k) _ (HcA x _) Hk' Hs' Ht'.
  have Hkn : (k =? aid (pa s))%nat = false by apply/Nat.eqb_neq; lia.
  by rewrite /= IHc /= Hkn andbF.
clear Hst x.
case: e Hb HeA Hop
  => // [? ? | ? ? ? | ? ? | ? ? ? | fa lo hi [s' | ? | ?] bi] //= Hb HeA Hop.
- case: eA HeA Hset Htl Hop => //= ? ? _ Hset Htl Hop.
  exact: Hop Hb Hset Htl.
- case: eA HeA Hset Htl Hop => //= ? ? ? _ Hset Htl Hop.
  exact: Hop Hb Hset Htl.
- case: eA HeA Hset Htl Hop => //= ? ? _ Hset Htl Hop.
  exact: Hop Hb Hset Htl.
- by case: eA HeA Hset Htl Hop.
case: Hb => _ [_ Hret].
case: eA HeA Hset Htl Hop => //= fa' lo' hi' i' bi' _ _ Htl _.
move: Htl.
have := HcA (PV (AV 0 false) (VInfo 0 Real None) dummy_tvar (VInt 0) 0)
  (let_binder k (AFold fa' lo' hi' i' bi')).
rewrite Hret; case: (cA _) => //= ? _.
by case: (tail_fold_live _ _ _).
Qed.
(* A step that gives its state back does not read it. *)
Lemma nbody_ret_dead L k (bP : pv -> pv -> anf pv bare) bA initA :
  (forall x y, nbody y (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  aset_tail (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) = false ->
  tail_fold_live cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) = None ->
  state_live cv k initA bA = false.
Proof.
move=> Hfb HbA Hset Htl.
rewrite /state_live /fold_binders.
set vr := fold_varied k initA bA in Hset Htl *.
set ix := PV (AV k false) (anon k) dummy_tvar (VInt 0%Z) 0.
set sx := PV (AV (S k) vr) (anon (S k)) dummy_tvar (VInt 0%Z) 0.
have Hsk : (aid (pa sx) < S (S k))%nat by rewrite /=; lia.
by rewrite (nbody_ret_needs sx (bP ix sx) (Hfb ix sx) (sx :: ix :: L) (S (S k))
  _ (HbA ix _ sx _) Hsk Hset Htl).
Qed.

(* So the state of a loop is live only when its step ends with a set. *)
Lemma nbody_live_set L k (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
  (forall x y, nbody y (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  (forall p, In p L -> aid (pa p) = vid (pw p)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) ->
  reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))) =
    false ->
  state_live cv k initA bA = true ->
  aset_tail (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) = true.
Proof.
move=> Hfb HbA HbW Hid Hk HtB Hra Hl.
set t := bA (AV k false) (AV (S k) (fold_varied k initA bA)).
case Es: (aset_tail (S (S k)) t) => //.
case Et: (tail_fold_live cv (S (S k)) t) => [l |].
  have Hn : tail_fold_live cv (S (S k)) t <> None by rewrite Et.
  by rewrite (nbody_state_dead L k bP bA bW initA z wP Hfb HbA HbW Hid Hk HtB
    Hra Hn) in Hl.
by rewrite (nbody_ret_dead L k bP bA initA Hfb HbA Es Et) in Hl.
Qed.

(* Facts on a let of an operation or a read. *)
Lemma is_op_eq {V1 V2 : Type} G (e1 : value V1 bare) (e2 : value V2 bare) :
  value_eq G e1 e2 -> is_op e1 -> is_op e2.
Proof. by case: e1; case: e2. Qed.

Lemma records_op k (e : value avar bare) : is_op e -> records cv k e = false.
Proof. by case: e. Qed.

Lemma tail_fold_live_op k a (e : value avar bare) c : is_op e ->
  tail_fold_live cv k (ALet a e c) = tail_fold_live cv (S k) (c (let_binder k
    e)).
Proof. by case: e. Qed.

Lemma aset_tail_op k a (e : value avar bare) c : is_op e ->
  aset_tail k (ALet a e c) = aset_tail (S k) (c (let_binder k e)).
Proof. by case: e. Qed.

Lemma tail_live_op k a (e : value avar bare) c : is_op e ->
  tail_live cv k (ALet a e c) = tail_live cv (S k) (c (let_binder k e)).
Proof. by move=> He; rewrite /tail_live tail_fold_live_op. Qed.

Lemma records_fold k fa lo hi init (b : avar -> avar -> anf avar bare) :
  records cv k (AFold fa lo hi init b) =
  state_live cv k init b ||
  records_in cv (S (S k)) (b (AV k false) (AV (S k) (fold_varied k init b))).
Proof. by []. Qed.

(* The innermost fold of a step is live iff the step records. *)
Lemma nbody_records s (bP : anf pv bare) : nbody s bP ->
  forall L k wP ix bA bW te,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW ->
  (forall p, In p L -> aid (pa p) = vid (pw p)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  typecheck (option_map (amap pw) wP) (ArrayBody (AVar (pw ix)) (AVar (pw s)))
    k bW = (te, Ok) ->
  records_in cv k bA = tail_live cv k bA.
Proof.
move: s bP; apply: nbody_ind.
- move=> s a e b' Hop Hb IH L k wP ix [aA eA cA | ?] [aW eW cW | ?] te //=.
  move=> [HeA HcA] [HeW HcW] Hid Hk Htc.
  case Hte: (typecheck_value _ _ _ _ eW) Htc => [te0 []] //= Htc.
  have HopA := is_op_eq _ _ _ HeA Hop.
  rewrite tail_live_op // records_op //=.
  set x := PV (let_binder k eA) (VInfo k te0 None) dummy_tvar (VInt 0) 0.
  apply: (IH x (x :: L) (S k) wP ix _ (cW (VInfo k te0 None)) te
    (HcA x _) (HcW x _)) => //.
  - by move=> p [<- | Hp] //; exact: Hid.
  by move=> p [<- | Hp] /=; [lia | have := Hk p Hp; lia].
- move=> s a aP iP vP b' Hr L k wP ix [aA eA cA | ?] [aW eW cW | ?] te //=.
  move=> [HeA HcA] _ _ _ _.
  case: eA HeA => //= a2 i2 v2 _.
  set x := PV (AV 0 false) (VInfo 0 Real None) dummy_tvar (VInt 0) 0.
  have := HcA x (let_binder k (ASet a2 i2 v2)); rewrite (Hr x) /tail_live /=.
  by case: (cA _).
- move=> s a fa lo hi bi b' Hbi IH Hr L k wP ix [aA eA cA | ?]
    [aW eW cW | ?] te //=.
  move=> [HeA HcA] [HeW HcW] Hid Hk Htc.
  case: eA HeA => // faA loA hiA iA biA [_ [_ [HiA HbiA]]].
  case: eW HeW Htc => // faW loW hiW iW biW [_ [_ [HiW HbiW]]] Htc.
  case: iA HiA => // ia /in_gA [HsL Eia]; subst ia.
  case: iW HiW Htc => // iw /in_gW [_ Eiw] Htc; subst iw.
  case Ete: (typecheck_value _ _ _ _ _) Htc => [te0 []] //= _.
  rewrite /= in Ete.
  case: (_ && _) Ete => // Ete.
  case: (ty_eqb _ Real) Ete => // Ete.
  case Ez: (vty (pw s)) Ete => [| | | z] // Ete.
  case: (WellFormed.is_tail cW k) Ete => // Ete.
  rewrite /= Nat.eqb_refl in Ete.
  case: (occurs_anf _ _ _) Ete => Ete.
    by case: (varg (pw s)) Ete => [[? ?] |].
  case HtB: (typecheck _ _ (S (S k)) _) Ete => [tb [| mm]] // Ete.
  case Etb: (ty_eqb tb (Array z)) Ete => // Ete.
  case Hrai: (reads_around_inner_loop _ _ _) Ete => // _.
  move/ty_eqb_true: Etb => Etb; subst tb.
  (* the continuation returns the fold *)
  set eA := AFold faA loA hiA (AVar (pa s)) biA.
  have [r EcA] : exists r, cA (let_binder k eA) = ARet r.
    set x := PV (AV 0 false) (VInfo 0 Real None) dummy_tvar (VInt 0) 0.
    have := HcA x (let_binder k eA); rewrite (Hr x).
    by case: (cA _) => // r _; exists r.
  rewrite /tail_live /= -/eA EcA /= orbF.
  (* the inner body *)
  set vr := fold_varied k (AVar (pa s)) biA.
  set xi := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
  set ys := PV (AV (S k) vr) (VInfo (S k) (Array z) None) dummy_tvar
    (VInt 0) 0.
  have Hid2 : forall p, In p (ys :: xi :: L) -> aid (pa p) = vid (pw p).
    by move=> p [<- | [<- | Hp]] //; exact: Hid.
  have Hk2 : forall p, In p (ys :: xi :: L) -> (vid (pw p) < S (S k))%nat.
    by move=> p [<- | [<- | Hp]] /=; [lia | lia | have := Hk p Hp; lia].
  have IHi := IH xi ys (ys :: xi :: L) (S (S k)) wP xi _ _ (Array z)
    (HbiA xi _ ys _) (HbiW xi _ ys _) Hid2 Hk2 HtB.
  rewrite /tail_live in IHi.
  have Esl : atom_member (AVar (AV (S k) vr))
      (snd (needs cv Replay (S (S k)) (biA (AV k false) (AV (S k) vr)))) =
      state_live cv k (AVar (pa s)) biA by [].
  rewrite Esl.
  case Et: (tail_fold_live cv (S (S k)) (biA (AV k false) (AV (S k) vr))) IHi
    => [l |] IHi.
    have Htl : tail_fold_live cv (S (S k)) (biA (AV k false) (AV (S k)
        (fold_varied k (AVar (pa s)) biA))) <> None by rewrite -/vr Et.
    rewrite (nbody_state_dead L k bi biA biW (AVar (pa s)) z wP Hbi HbiA HbiW
      Hid Hk HtB Hrai Htl).
    by rewrite IHi.
  by rewrite IHi orbF.
by move=> s L k wP ix [? ? ? | ?] [? ? ? | ?].
Qed.

Lemma tail_fold_state_op k a (e : value avar bare) c : is_op e ->
  tail_fold_state cv k (ALet a e c) =
  tail_fold_state cv (S k) (c (let_binder k e)).
Proof. by case: e. Qed.

(* The outer loop records iff it is live. *)
Lemma records_fold_nbody L k fa (loA hiA : atom avar)
  (bP : pv -> pv -> anf pv bare) bA bW initA z wP :
  (forall x y, nbody y (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  (forall p, In p L -> aid (pa p) = vid (pw p)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) ->
  reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))) =
    false ->
  records cv k (AFold fa loA hiA initA bA) = fold_live cv k initA bA.
Proof.
move=> Hfb HbA HbW Hid Hk HtB Hra.
rewrite records_fold /fold_live /fold_binders.
set vr := fold_varied k initA bA.
set xi := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set ys := PV (AV (S k) vr) (VInfo (S k) (Array z) None) dummy_tvar (VInt 0) 0.
have Hid2 : forall p, In p (ys :: xi :: L) -> aid (pa p) = vid (pw p).
  by move=> p [<- | [<- | Hp]] //; exact: Hid.
have Hk2 : forall p, In p (ys :: xi :: L) -> (vid (pw p) < S (S k))%nat.
  by move=> p [<- | [<- | Hp]] /=; [lia | lia | have := Hk p Hp; lia].
have Hr := nbody_records ys (bP xi ys) (Hfb xi ys) (ys :: xi :: L) (S (S k))
  wP xi _ _ (Array z) (HbA xi _ ys _) (HbW xi _ ys _) Hid2 Hk2 HtB.
rewrite /tail_live in Hr.
change (bA (pa xi) (pa ys)) with (bA (AV k false) (AV (S k) vr)) in Hr.
rewrite Hr.
case Et: (tail_fold_live cv (S (S k)) (bA (AV k false) (AV (S k) vr)))
  => [l |]; last by rewrite orbF.
have Htl : tail_fold_live cv (S (S k)) (bA (AV k false) (AV (S k)
    (fold_varied k initA bA))) <> None by rewrite -/vr Et.
by rewrite (nbody_state_dead L k bP bA bW initA z wP Hfb HbA HbW Hid Hk HtB
  Hra Htl).
Qed.

(* A step ending with an inner fold, on a varied state: its tail fold
   state is its liveness. *)
Lemma nbody_tail_state s (bP : anf pv bare) : nbody s bP ->
  forall L k bA, anf_eq (gA L) bP bA -> avaried (pa s) = true ->
  tail_fold_live cv k bA <> None ->
  tail_fold_state cv k bA = tail_fold_live cv k bA.
Proof.
elim: bP s => [a e b' IH | x] s Hb L k [aA eA cA | ?] // [HeA HcA] Hvs Htl.
have HopA : is_op e -> is_op eA := is_op_eq _ _ _ HeA.
have Hrec : (forall y, nbody s (b' y)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) <> None ->
    tail_fold_state cv (S k) (cA (let_binder k eA)) =
    tail_fold_live cv (S k) (cA (let_binder k eA)).
  move=> Hb' Ht'.
  set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
  exact: (IH x s (Hb' x) (x :: L) (S k) _ (HcA x _) Hvs Ht').
have Hop : is_op e -> (forall y, nbody s (b' y)) ->
    tail_fold_state cv k (ALet aA eA cA) = tail_fold_live cv k (ALet aA eA cA).
  move=> He Hb'; have HeA' := HopA He.
  rewrite tail_fold_live_op // in Htl.
  by rewrite tail_fold_state_op // tail_fold_live_op //; exact: Hrec.
case: e Hb HeA HopA Hop
  => // [? ? | ? ? ? | ? ? | ? ? ? | fa lo hi [s' | ? | ?] bi] Hb HeA HopA Hop;
  try by apply: Hop.
- case: eA HeA Htl Hrec Hop HopA => //= a2 i2 v2 _ Htl _ _ _.
  exfalso; apply: Htl.
  set x := PV (AV 0 false) (VInfo 0 Real None) dummy_tvar (VInt 0) 0.
  have := HcA x (let_binder k (ASet a2 i2 v2)); rewrite (Hb x).
  by case: (cA _).
case: Hb => Es [_ Hret]; subst s'.
case: eA HeA Htl Hrec Hop HopA
  => //= faA loA hiA [ia | ? | ?] biA [_ [_ [HiA _]]] Htl _ _ _ //.
move/in_gA: HiA => [_ Eia]; subst ia.
set eA := AFold faA loA hiA (AVar (pa s)) biA.
set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have := HcA x (let_binder k eA); rewrite (Hret x).
case: (cA _) => [? ? ? | [y | ? | ?]] //= [Ey | /in_gA [_ Ey]].
  by case: Ey => <-; rewrite Nat.eqb_refl Hvs /fold_live /=;
    case: (tail_fold_live _ _ _).
by rewrite Ey Nat.eqb_refl Hvs /fold_live /=; case: (tail_fold_live _ _ _).
Qed.

(* The replay of a step keeps the variables opened before it. *)
Lemma adj_replay_nbody s (bP : anf pv bare) : nbody s bP ->
  forall L k w vo bA bT se c, anf_eq (gA L) bP bA -> anf_eq (gT L) bP bT ->
  let '((fb, _), _) := open_pairs (adj W w vo Replay (rebuild _ bT
    (annotate_body_t cv Replay k bA)) se) c in
  forall s s1, run fb s = Some s1 -> forall v, below c v -> consistent v ->
    store_get s1 (keyv v) = store_get s (keyv v).
Proof.
elim: bP s => [a e cP IH | x] s //= Hab L k w vo bA bT se c HA HT; last first.
  case: bA HA => [? ? ? | ?] //= _; case: bT HT => [? ? ? | ?] //= _.
  by move=> s0 s1; rewrite /run /= => -[<-].
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
case: bT HT => [aT eT cT | ?] //= [HeT HcT].
cbn [annotate_body_t].
case Enl: (needs cv Replay (S k) (cA (let_binder k eA))) => [u l].
have Cc : consistent (DBound (c, c) : dvar W) by [].
(* a defined variable is fresh: the variables below c keep their values *)
have Hdef : forall so e0 s0 sa v, run [DDefine so (DBound (c, c)) e0] s0 = Some
  sa -> below c v -> consistent v ->
    store_get sa (keyv v) = store_get s0 (keyv v).
  move=> so e0 s0 sa v /run_define_inv [w0 ->] Hb Hcv.
  apply: store_get_set_other => K.
  by move: (keyv_inj _ _ Cc Hcv K) Hb => <- /=; lia.
(* the rest of the body, opened at S c *)
have Hrest : (forall y, nbody s (cP y)) -> forall t vr,
  let '((fb', _), _) := open_pairs (adj W w vo Replay (rebuild _ (cT (open_let t
    (DBound (c, c)) vr false))
                           (annotate_body_t cv Replay (S k) (cA (let_binder k
                             eA)))) se) (S c) in
  forall s s1, run fb' s = Some s1 -> forall v, below (S c) v -> consistent v ->
    store_get s1 (keyv v) = store_get s (keyv v).
  move=> Hb t vr.
  exact: (IH (PV (let_binder k eA) (VInfo k Real None)
    (open_let t (DBound (c, c)) vr false) (VInt 0) 0) s (Hb _) (_ :: L) (S k)
    w vo _ _ se (S c) (HcA _ _) (HcT _ _)).
case: e Hab HeA HeT
  => // [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0 | fa0 lo0 hi0 i0 bi0] Hab HeA HeT.
(* an operation or a read: the replay defines its binder, if needed, then
   replays the rest *)
1-3: have := Hrest Hab (type_of (rebuild_value _ eT TLeaf))
    (varied_value k eA);
  destruct eA; try contradiction; destruct eT; try contradiction;
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs];
  rewrite !open_pairs_sbind;
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr;
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _);
  cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv;
  move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun;
  rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c))
    Hcv);
  first [exact: (Hdef _ _ _ _ _ Er) | by move: Er; rewrite /run /= => -[<-]].
(* the final set: the reverse sweep does not read it (needs of a return in
   Replay is empty), so it is not replayed *)
- case: eA HeA Enl HcA Hrest => // a1 i1 v1 _ Enl HcA _; case: eT HeT HcT => //
  a2 i2 v2 _ HcT.
  have El : l = [].
    have := HcA (PV (let_binder k (ASet a1 i1 v1)) (VInfo k Real None)
      dummy_tvar (VInt 0) 0) (let_binder k (ASet a1 i1 v1)).
    rewrite Hab; move: Enl; case: (cA _) => //= r [_ <-] _; reflexivity.
  rewrite El /=.
  have EcT : forall y, exists r, cT y = ARet r.
    by move=> y; have := HcT (PV (AV k false) (VInfo k Real None) y (VInt 0) 0)
      y; rewrite Hab; case: (cT y) => //= r _; exists r.
  case: a2 => [a3 | s3 | z3] /=.
  all: cbn [open_pairs]; rewrite ?open_pairs_sbind.
  + case: (EcT (open_let (tty a3) (tstored a3) (varied a1 || varied v1)
    (trecorded a3))) => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
  + case: (EcT (open_let Real (DBound (c, c)) (varied a1 || varied v1) false))
    => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
  + case: (EcT (open_let Integer (DBound (c, c)) (varied a1 || varied v1)
    false)) => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
(* the final fold: the reverse sweep does not read it (needs of a return in
   Replay is empty), so it is not replayed *)
case: eA HeA Enl HcA Hrest => // fa1 lo1 hi1 i1 b1 _ Enl HcA _.
case: eT HeT HcT => // fa2 lo2 hi2 i2 b2 _ HcT.
case: (i0) Hab => [s0 | ? | ?] // [_ [_ Hret]].
have El : l = [].
  have := HcA (PV (let_binder k (AFold fa1 lo1 hi1 i1 b1)) (VInfo k Real None)
    dummy_tvar (VInt 0) 0) (let_binder k (AFold fa1 lo1 hi1 i1 b1)).
  by rewrite Hret; move: Enl; case: (cA _) => //= r [_ <-] _.
rewrite El /=.
have EcT : forall y, exists r, cT y = ARet r.
  move=> y; have := HcT (PV (AV k false) (VInfo k Real None) y (VInt 0) 0) y.
  by rewrite Hret; case: (cT y) => //= r _; exists r.
case: i2 => [a3 | s3 | z3] /=.
all: cbn [open_pairs]; rewrite ?open_pairs_sbind.
+ set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
  case Ety: (tty a3) => [| | | z0].
  - cbn [open_pairs].
    case: (EcT (open_let Real (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  - cbn [open_pairs].
    case: (EcT (open_let Integer (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  - cbn [open_pairs].
    case: (EcT (open_let Boolean (DBound (c, c)) vr false)) => r ->.
    cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
    case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
    by move=> s1 s2; rewrite /run /= => -[<-].
  case: (EcT (open_let (Array z0) (tstored a3) vr (trecorded a3))) => r ->.
  cbn [rebuild adj sweep_eqb sbind]; rewrite open_pairs_sbind.
  case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
  by move=> s1 s2; rewrite /run /= => -[<-].
+ set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
  case: (EcT (open_let Real (DBound (c, c)) vr false)) => r ->.
  cbn [rebuild adj sweep_eqb open_pairs sbind]; rewrite open_pairs_sbind.
  case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
  by move=> s1 s2; rewrite /run /= => -[<-].
set vr := varied i1 || varied_anf (S (S k)) (b1 (fresh k) (fresh (S k))).
case: (EcT (open_let Integer (DBound (c, c)) vr false)) => r ->.
cbn [rebuild adj sweep_eqb open_pairs sbind]; rewrite open_pairs_sbind.
case: (open_pairs (if _ then _ else _) _) => [? ?]; cbn [open_pairs].
by move=> s1 s2; rewrite /run /= => -[<-].
Qed.

(* The reverse sweep of a step ending with a set or giving its state back
   writes only adjoints. *)
Lemma adj_rev_bars_nbody s (bP : anf pv bare) : nbody s bP ->
  forall L k bA (t : ltree) w vo bT se c, anf_eq (gA L) bP bA ->
  tail_fold_live cv k bA = None -> anf_eq (gT L) bP bT ->
  Forall bar_stmt (snd (fst (open_pairs (adj W w vo Replay (rebuild _ bT t) se)
    c))).
Proof.
elim: bP s => [a e cP IH | x] s Hab L k bA t w vo bT se c HA Htl HT;
  rewrite /= in Hab; last first.
  case: bT HT => [? ? ? | r] //= _.
  cbn [rebuild adj sweep_eqb open_pairs snd fst].
  case: (tof r) => //; case Eb: (bar r) => [bx |] //.
  have [x0 [-> Hx]] := bar_some _ _ Eb.
  by constructor=> //; constructor.
case: bT HT => [aT eT cT | ?] // [HeT HcT].
case: bA HA Htl => [aA eA cA | ?] // [HeA HcA] Htl.
have Htl' : is_op eA ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) = None.
  by move=> Hop; rewrite -(tail_fold_live_op k aA).
have [aa [vt [rest ->]]] : exists aa vt rest,
    rebuild _ (ALet aT eT cT) t = ALet aa (rebuild_value _ eT vt) (fun v =>
      rebuild _ (cT v) rest).
  by case: t => [aa vt rest|]; [exists aa, vt, rest | exists no_ann, TLeaf,
    TRet].
have Hbd : forall t0 (m : dvar W), Forall bar_stmt (bar_declaration W t0 m).
  by case=> * //=; do 2 constructor.
have HopA : is_op e -> is_op eA := is_op_eq _ _ _ HeA.
(* the reverse sweep of a straight value writes only adjoints *)
have Hre : straight_value e -> forall tr te n c0,
    Forall bar_stmt (fst (open_pairs (rev_value W w vo
      (rebuild_value _ eT tr) te n) c0)).
  by move=> Hs tr te n c0; apply: (straight_rev_bars e Hs L) HeT.
case: e Hab HeT HeA HopA Hre
  => // [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0 | fa0 lo0 hi0 i0 bi0] Hab HeT
  HeA HopA Hre.
(* an operation or a read *)
1-3: have Hop := HopA I; destruct eT; try contradiction;
  cbn [rebuild_value adj with_storage];
  case: (let_ann aa) => [[vv ac] cc]; cbn [open_pairs];
  rewrite !open_pairs_sbind;
  lazymatch goal with |- context [open_let ?t (DBound ?d) ?vv false] =>
    have := IH (PV (let_binder k eA) (VInfo 0 Real None)
      (open_let t (DBound d) vv false) (VInt 0) 0) s (Hab _) (_ :: L)
      (S k) _ rest w vo _ se (S c) (HcA _ _) (Htl' Hop) (HcT _ _) end;
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr;
  have {}Hre := Hre I TLeaf Real (DBound (c, c)) c3;
  case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
  try (apply: Forall_cons; first by []);
  rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr;
  try exact: Hre; try by [].
(* the final set: the rest returns the variable *)
- case: eT HeT HcT Hre => // a2 i2 v2 HeT HcT Hre.
  have Hret : forall y t0 c0, Forall bar_stmt (snd (fst (open_pairs
      (adj W w vo Replay (rebuild _ (cT y) t0) se) c0))).
    move=> y t0 c0.
    have := HcT (PV (AV 0 false) (VInfo 0 Real None) y (VInt 0) 0) y.
    rewrite Hab; case: (cT y) => //= r _.
    cbn [rebuild adj sweep_eqb open_pairs snd fst].
    case: (tof r) => //; case Eb: (bar r) => [bx|] //.
    have [x0 [-> Hx]] := bar_some _ _ Eb.
    by constructor=> //; constructor.
  have {}Hre := Hre I TLeaf.
  cbn [rebuild_value adj]; case: (let_ann aa) => [[vv ac] cc].
  case: a2 HeT Hre => [a3 | s3 | z3] HeT Hre; cbn [with_storage open_pairs];
    rewrite !open_pairs_sbind.
  + have := Hret (open_let (tty a3) (tstored a3) vv (trecorded a3)) rest c.
    case: (open_pairs _ c) => [[fb' rb'] c3] /= IHr.
    have {}Hre := Hre (tty a3) (tstored a3) c3.
    case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
      try (apply: Forall_cons; first by []);
      rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr;
      try exact: Hre; try by [].
  + have := Hret (open_let Real (DBound (c, c)) vv false) rest (S c).
    case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
    have {}Hre := Hre Real (DBound (c, c)) c3.
    case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
      try (apply: Forall_cons; first by []);
      rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr;
      try exact: Hre; try by [].
  have := Hret (open_let Integer (DBound (c, c)) vv false) rest (S c).
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
  have {}Hre := Hre Integer (DBound (c, c)) c3.
  case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
    try (apply: Forall_cons; first by []);
    rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr;
    try exact: Hre; try by [].
(* the final fold: its tail fold is live *)
case: (i0) Hab => [s0 | ? | ?] // [_ [_ Hret]].
case: eA HeA Htl Htl' HopA => // faA loA hiA iA biA _ Htl _ _.
move: Htl => /=.
have := HcA (PV (AV 0 false) (VInfo 0 Real None) dummy_tvar (VInt 0) 0)
  (let_binder k (AFold faA loA hiA iA biA)).
rewrite Hret; case: (cA _) => //= ? _.
by case: (tail_fold_live _ _ _).
Qed.

Lemma body_pushes_op aD eD cD ve st :
  is_op eD -> aeval_value (duals reals) eD = Some ve ->
  body_pushes (ALet aD eD cD) st = body_pushes (cD ve) st.
Proof.
move=> Hop Ev; rewrite /= Ev.
by case: eD Hop Ev => // *; case: (cD ve).
Qed.

(* The tail tape of a step: when the step ends with a live inner fold, the
   tape of the storage holds, on top, what that fold pushed, and the storage
   its value. *)
Lemma tail_tape_nbody sx (bP : anf pv bare) : nbody sx bP ->
  forall L k bA bD s n R v0,
  anf_eq (gA L) bP bA -> anf_eq (gD L) bP bD -> In sx L ->
  (forall p, In p L -> pa p = pa sx -> p = sx) ->
  (forall p, In p L -> (aid (pa p) < k)%nat) ->
  is_array (vty (pw sx)) ->
  aeval (duals reals) bD = Some v0 ->
  (tail_live cv k bA = true -> store_get s (keyv n) = Some (primal v0)) ->
  (tail_live cv k bA = true -> store_get s (keyv (TapeOf n)) =
     Some (VTape (rev (body_pushes bD (pd sx)) ++ R))) ->
  tail_tape cv k L bP bA bD s n.
Proof.
elim: bP => [a e c IH | x]; last by move=> _ L k bA bD *; rewrite /=.
move=> Hfb L k [aA eA cA | ?] [aD eD cD | ?] s n R v0
  // [HeA HcA] [HeD HcD] HsL Hu Hk Hsa Hev Hn Ht.
rewrite /= in Hev.
have [ve Ev] : exists ve, aeval_value (duals reals) eD = Some ve.
  by move: Hev; case: (aeval_value _ eD) => [ve |] // _; exists ve.
rewrite Ev /= in Hev.
set xv := PV (AV 0 false) (anon 0) dummy_tvar ve 0.
have HopA : is_op e -> is_op eA := is_op_eq _ _ _ HeA.
(* a scalar let: the tape is the one of the rest of the step *)
have Hop : is_op e -> (forall y, nbody sx (c y)) ->
    tail_tape cv k L (ALet a e c) (ALet aA eA cA) (ALet aD eD cD) s n.
  move=> He Hb; have HeA' := HopA He.
  have HeD' : is_op eD := is_op_eq _ _ _ HeD He.
  split.
    move=> _ eW _.
    by case: eA HeA HeA' {HopA HcA Hn Ht} => //= *; case: eW; case: eD.
  move=> y Ey Eyv.
  have Ev' : ve = pd y by move: Ev; rewrite Eyv => -[].
  apply: (IH y (Hb y) (y :: L) (S k) _ _ s n R v0) => //.
  - by rewrite /= Ey; exact: HcA.
  - exact: HcD.
  - by right.
  - move=> p [<- | Hp] E; last exact: Hu.
    by have := Hk sx HsL; rewrite -E Ey /=; lia.
  - by move=> p [<- | Hp]; [rewrite Ey /=; lia | have := Hk p Hp; lia].
  - by rewrite -Ev'.
  - by move=> El; apply: Hn; rewrite tail_live_op.
  move=> El; have El2 : tail_live cv k (ALet aA eA cA) = true.
    by rewrite tail_live_op.
  rewrite (Ht El2).
  by rewrite (body_pushes_op _ _ _ _ _ HeD' Ev) Ev'.
case: e Hfb HeA HeD Hop HopA
  => // [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0' | fa lo hi [s0 | ? | ?] bi]
  Hfb HeA HeD Hop HopA; try by apply: Hop.
(* the set ending the step: no fold *)
- case: eA HeA HopA Hn Ht Hop => // ? ? ? _ _ _ _ _.
  by split=> [_ eW _ | y _ _]; [case: eW | rewrite Hfb].
(* the inner fold, on the state sx *)
case: Hfb => [Es0 [_ Hret]]; subst s0; clear Hop HopA.
have [r EcA] : exists r, cA (let_binder k eA) = ARet r.
  have := HcA xv (let_binder k eA); rewrite Hret.
  by case: (cA _) => // r _; exists r.
have EcD : cD ve = ARet (AVar ve).
  have := HcD (PV (let_binder k eA) (anon 0) dummy_tvar ve 0) ve.
  rewrite Hret; case: (cD ve) => // -[d | ? | ?] //= [[<-] // | /in_gD [_ ->]].
  by [].
rewrite EcD /= in Hev; case: Hev => Ev0; subst v0.
have Etl : tail_live cv k (ALet aA eA cA) =
    match eA with
    | AFold _ _ _ initA bA0 => fold_live cv k initA bA0
    | _ => tail_live cv k (ALet aA eA cA)
    end.
  case: (eA) EcA => // ? ? ? initA bA0 EcA.
  by rewrite /tail_live /= EcA /fold_live /=; case: (tail_fold_live _ _ _).
case: eA HeA Etl EcA Hn Ht
  => // fa' loA hiA iA biA [_ [_ [HiA _]]] Etl EcA Hn Ht.
move/atom_graph: HiA => [EiA _]; subst iA.
case: eD HeD Ev EcD Ht => // fd loD hiD iD biD [HloD [HhiD [HiD _]]] Ev EcD Ht.
case: iD HiD Ev Ht => // dd /in_gD [_ Edd] Ev Ht; subst dd.
split; last by move=> y _ _; rewrite Hret.
move=> _ eW HeW.
case: eW HeW => // fw loW hiW [w | ? | ?] biW [_ [_ [HiW _]]] //.
move/in_gW: HiW => [_ Ew]; subst w.
rewrite /fold_tape.
move: Ev; rewrite /=.
case Hlo: (aeval_atom _ loD) => [[| l | | |] |] //.
case Hhi: (aeval_atom _ hiD) => [[| h | | |] |] // Ev.
move=> tr Htr; split.
  by move: Hsa; rewrite /=; case: (vty (pw sx)).
move=> _ El; rewrite -Etl in El.
split.
  exists R; rewrite (Ht El) /= Hlo Hhi Ev EcD Htr fold_pushes_fix.
  by [].
by move=> ve'; rewrite Ev => -[<-]; exact: Hn.
Qed.

(* A step whose analysed instance ends with a set is an abody. *)
Lemma nbody_abody s (bP : anf pv bare) : nbody s bP ->
  forall G k bA, anf_eq G bP bA -> aset_tail k bA = true -> abody bP.
Proof.
elim: bP s => [a e b' IH | x] s Hb G k [aA eA cA | ?] // [HeA HcA] Hset.
have HopA : is_op e -> is_op eA := is_op_eq _ _ _ HeA.
have Hop : is_op e -> (forall x, nbody s (b' x)) -> forall x, abody (b' x).
  move=> He Hb' x; rewrite (aset_tail_op _ _ _ _ (HopA He)) in Hset.
  exact: (IH x s (Hb' x) _ (S k) _ (HcA x (let_binder k eA)) Hset).
case: e Hb HeA HopA Hop
  => // [? ? | ? ? ? | ? ? | fa lo hi [s' | ? | ?] bi] Hb HeA HopA Hop //;
  try by apply: Hop.
by case: eA HeA Hset HopA Hop.
Qed.

(* The outer loop of a nest: its step ends with its live innermost fold. *)
Lemma tail_state_nbody L k (bP : pv -> pv -> anf pv bare) bA initA :
  (forall x y, nbody y (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  fold_varied k initA bA = true ->
  tail_fold_live cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) <> None ->
  tail_fold_state cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) =
    Some (fold_live cv k initA bA) /\
  tail_live cv (S (S k))
    (bA (AV k false) (AV (S k) (fold_varied k initA bA))) =
    fold_live cv k initA bA.
Proof.
move=> Hfb HbA Hvr Htl.
set vr := fold_varied k initA bA in Hvr Htl *.
set ix := PV (AV k false) (anon k) dummy_tvar (VInt 0%Z) 0.
set sx := PV (AV (S k) vr) (anon (S k)) dummy_tvar (VInt 0%Z) 0.
have Hts := nbody_tail_state sx (bP ix sx) (Hfb ix sx) (sx :: ix :: L)
  (S (S k)) _ (HbA ix _ sx _) Hvr Htl.
change (bA (pa ix) (pa sx)) with (bA (AV k false) (AV (S k) vr)) in Hts.
rewrite Hts /tail_live /fold_live /fold_binders -/vr.
by case: (tail_fold_live _ _ _) Htl.
Qed.

(* The typing of a fold updating an array in place. *)
Lemma tc_fold_inplace wr p tail k fa (lo hi : atom vinfo) (w : vinfo)
  (bW : vinfo -> vinfo -> anf vinfo bare) te : is_array (vty w) ->
  typecheck_value wr p tail k (AFold fa lo hi (AVar w) bW) = (te, Ok) ->
  exists z, vty w = Array z /\ te = Array z /\
  typecheck wr (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) =
    (Array z, Ok) /\
  reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k))) = false.
Proof.
move=> Ha; rewrite /=.
case: (_ && _) => //.
case Ez: (vty w) Ha => [| | | z] //= _.
case: (in_place_init _ _ _ _) => //.
case: (occurs_anf _ _ _) => //; first by case: (varg w) => [[? ?] |].
case HtB: (typecheck _ _ _ _) => [tb [| mm]] //.
case Etb: (ty_eqb tb (Array z)) => //.
case Hra: (reads_around_inner_loop _ _ _) => // -[<-].
move/ty_eqb_true: Etb HtB => -> HtB.
by exists z.
Qed.

(* The inner in-place fold that ends the body of the outer loop: it updates
   the state in place, pushing the elements its steps overwrite. *)
Lemma psim_fold_nbody a a' (loP hiP : atom pv) (s : pv)
  (bi : pv -> pv -> anf pv bare) (cP : pv -> anf pv bare) :
  is_array (vty (pw s)) -> (forall x y, nbody y (bi x y)) ->
  (forall x y, psim_body cv (bi x y)) ->
  (forall x, cP x = ARet (AVar x)) ->
  psim_body cv (ALet a (AFold a' loP hiP (AVar s) bi) cP).
Proof.
move=> Hsa Hbi Hpsb HcP L k c st wP pp m m'.
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
have [z [_ [_ [HtB Hrai]]]] := tc_fold_inplace _ _ _ _ _ _ _ _ _ _ Hsa Hte.
have Hid : forall p, In p L -> aid (pa p) = vid (pw p).
  by move=> p Hp; case: (static_in _ _ _ HL Hp).
have Hk : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [_ [Hlt _]] := static_in _ _ _ HL Hp.
have Hrecs : records cv k eA = true -> fold_live cv k (AVar (pa s)) bA = true.
  by rewrite (records_fold_nbody L k fa loA hiA bi bA bW (AVar (pa s)) z wP
    Hbi HbA HbW Hid Hk HtB Hrai).
(* the forward sweep of the fold *)
have IHf := afwd_fold_body cv a' loP hiP (AVar s) bi
  (ex_intro _ s (conj erefl Hsa)) Hpsb (fun x y => nbody_act _ _ (Hbi x y))
  (fun x y => nbody_ibody _ _ (Hbi x y)).
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

(* The forward computation of a step. *)
Lemma nbody_psim s b : nbody s b -> psim_body cv b.
Proof.
move: s b; apply: nbody_ind.
- move=> s a e b' Hop _ IH.
  case: e Hop => //= [f x | f x y | x i] _.
  + by apply: psim_let; [exact: afwd_op1 | exact: act_op1 | by [] | by [] |].
  + by apply: psim_let; [exact: afwd_op2 | exact: act_op2 | by [] | by [] |].
  by apply: psim_let; [exact: afwd_get | exact: act_get | by [] | by [] |].
- by move=> s a aP iP vP b' _; exact: psim_set_let.
- move=> s a fa lo hi bi b' Hbi IH Hr.
  case: (array_or_not s) => Ha.
    exact: psim_fold_nbody.
  have Hna : forall p, AVar s = AVar p -> ~ is_array (vty (pw p)).
    by move=> p [<-].
  apply: psim_let.
  - by apply: afwd_fold => // x y; exact: nbody_act (Hbi x y).
  - by apply: act_fold => // x y; exact: nbody_act (Hbi x y).
  - move=> wP tail /=; case: (vty (pw s)) Ha => // z Ha.
    by exfalso; apply: Ha.
  - by [].
  by move=> x; rewrite Hr; exact: psim_ret.
by move=> s; exact: psim_ret.
Qed.

(* The forward sweep of an in-place fold whose steps are nbodies. *)
Lemma afwd_fold_nbody a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, nbody y (bP x y)) -> asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> Hq Hb; apply: afwd_fold_body => // x y.
- exact: nbody_psim (Hb x y).
- exact: nbody_act (Hb x y).
exact: nbody_ibody (Hb x y).
Qed.

(* The reverse sweep of an in-place fold whose steps are nbodies: a step
   ending with a set pops the element it overwrote when the state is
   recorded; a step ending with an inner fold gives the state back through
   it; otherwise the state is not touched. *)
Lemma arev_fold_nbody a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, nbody y (bP x y)) -> (forall x y, asim_body cv (bP x y)) ->
  asim_rev cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab Hasb L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT
  HD Hs Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr.
case: eA HA Hvr => // ann loA hiA iA bA [HloA [HhiA [HiA HbA]]] Hvr.
case: eW HW Htc Hs => // ann0 loW hiW iW bW [HloW [HhiW [HiW HbW]]] Htc Hs.
case: eT HT => // ann1 loT hiT iT bT [HloT [HhiT [HiT HbT]]].
case: eD HD Hev => // ann2 loD hiD iD bD [HloD [HhiD [HiD HbD]]] Hev.
move/atom_graph: HloA => [ElA HloL]; move/atom_graph: HhiA => [EhA HhiL].
move/atom_graph: HloW => [ElW _]; move/atom_graph: HhiW => [EhW _].
move/atom_graph: HloT => [ElT _]; move/atom_graph: HhiT => [EhT _].
move/atom_graph: HloD => [ElD _]; move/atom_graph: HhiD => [EhD _].
subst loA hiA loW hiW loT hiT loD hiD.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
case: iA HiA Hvr => // ia /in_gA [HqL Eia] Hvr; subst ia.
case: iW HiW Htc Hs => // iw /in_gW [_ Eiw] Htc Hs; subst iw.
case: iT HiT => // it /in_gT [_ Eit]; subst it.
case: iD HiD Hev => // id /in_gD [_ Eid] Hev; subst id.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
  ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
(* the array is the one the place updates in place *)
have [Hown Etail] : owner wP pp = Some q /\ tail = true.
  case: pp Hs Htc => [| | | ix0 sx0] Hs Htc; case Et: tail Htc => //= Htc.
  - case Ew: wP Hs Htc => [y |] //= Hs Htc.
    case E: (match amap pw y with
      | AVar y0 => (vid (pw q) =? vid y0)%nat | _ => false end) Htc => // Htc.
    have [->] := unique_written_s _ _ _ _ _ _ _ _ _ Hs HqL erefl E.
    by rewrite /= Eqz.
  case E: (vid (pw q) =? vid (pw sx0))%nat Htc => // Htc.
  have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
  by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs HqL Hsx E).
subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true
    (AVar (pw q)) = true.
  by case: (in_place_init _ _ _ _) Htc.
rewrite Hin_pl in Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k)))) Htc
  => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP)
    (ArrayBody (AVar (VInfo k Integer None))
       (AVar (VInfo (S k) (Array z) None)))
    (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc
  => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case Hrai: (reads_around_inner_loop (S k) (S (S k))
  (bW (anon k) (anon (S k)))) Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => <-.
subst n; rewrite /= Eqz in Hst; set n := DBound (j, j) in Hst Hev Hvr *.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn z0 =>
  (eq_refl : rev_value W w vo (AFold (FoldAnn sv live0 recs) lo hi init b)
     (Array z0) nn =
   Fresh "i" (fun i =>
     let '(ix, sx) := open_fold sv (Array z0) nn (DBound i) false in
     sbind (adj W w vo Replay (b ix sx) (DReal "0")) (fun sw =>
       Done (rev_loop W (DBound i) (spell lo) (spell hi)
               (if live0 then [DPop (TapeOf nn)
                  (DAt (DVar nn) (tail_index W (b ix sx)))] else [])
               [] sw))))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
  case Hob: (@open_pairs A t (S c)) => [[fb rb] c2] end.
have Hc2 : (S c <= c2)%nat.
  by lazymatch type of Hob with @open_pairs _ ?t _ = _ =>
    have := open_pairs_mono t (S c); rewrite Hob end.
cbn [open_pairs]; split; first by lia.
move=> s2 O Hrd Hr Hns Htp Hft Hrec.
(* the fold updates in place the written argument q, at the top, or the state
   q of an enclosing in-place loop, ending its body *)
have Hpl : pp = PTop \/ exists ix0 sx0, pp = PArray ix0 sx0.
  case Epp: pp Hown => [| | | ix0 sx0] //= _; first by left.
  by right; exists ix0, sx0.
have {}Hft := Hft Hpl.
have Hlivq :
    live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) q.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
have Hqa' : is_array (vty (pw q)) by rewrite Eqz.
have Hvq : avaried (pa q) = true.
  case: Hpl => [Epp | [ix0 [sx0 Epp]]]; move: Hown Hs; rewrite Epp.
    case Ew: wP => [[y | |] |] //= + Hs.
    case: (vty (pw y)) => // [z0] [Eyq]; subst y.
    exact: (proj2 (s_top _ _ _ _ _ _ _ Hs q erefl erefl Hqa') Hlivq).
  move=> /= [<-] Hs.
  by have [_ [_ [_ [_ [-> _]]]]] := s_place _ _ _ _ _ _ _ Hs.
have HqO : In (tangent (pd q), n) O.
  by rewrite Hst; exact: (r_owner _ _ _ _ _ _ _ Hr q Hown).
have HnO : In n (map snd O) by apply/in_map_iff; exists (tangent (pd q), n).
have Eput : oput O n (tangent ve) = oset O n (tangent ve).
  by rewrite /oput; case: in_dec.
rewrite Eput.
have {}Hrec : not_in_loop pp ->
    records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) =
      false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Er; apply: (Hrec Hnl _ q Hown Hvq Er); rewrite /= Eqz.
(* the states of the fold *)
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev
  => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev
  => [[| h | | |] |] // Hev.
have [tr Htr] := fold_trace_exists _ _ _ _ _ Hev.
set dflt := VReal (Dual 0 0).
have [Hlen [Hst0 Hstep]] := fold_trace_step _ _ _ _ _ _ dflt Hev Htr.
set N := count l h.
set st := fun jn => nth jn (tr ++ [ve]) dflt.
have HidL : forall p, In p L -> aid (pa p) = vid (pw p).
  by move=> p Hp; case: (static_in _ _ _ HL Hp).
have HkL : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [_ [Hlt _]] := static_in _ _ _ HL Hp.
(* the tape of the loop: the pushes of its steps, last first, when it
   records *)
set live := fold_live cv k (AVar (pa q)) bA.
have Hrecs : records cv k
    (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) = live.
  exact: (records_fold_nbody L k ann _ _ bP bA bW _ z wP Hab HbA HbW HidL HkL
    HtB Hrai).
have [rest [Htape0 Hn_live]] : exists rest,
    (live = true -> store_get s2 (keyv (TapeOf n)) =
       Some (VTape (rev (fold_pushes bD l tr) ++ rest))) /\
    (live = true -> store_get s2 (keyv n) = Some (primal ve)).
  move: Hft; rewrite /fold_tape Hlo Hhi.
  change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
  move=> /(_ tr Htr) [_ Ha].
  have Har : is_array (of_atom (AVar (pw q))) by rewrite /= Eqz.
  case El: live; last by exists [].
  have [[rest Ht] Hv] := Ha Har El.
  by exists rest; split=> _; [exact: Ht | exact: Hv ve Hev].
have Hn_dead : not_in_loop pp -> live = false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Hl; apply: Hrec Hnl _; rewrite Hrecs.
(* the states of the fold are arrays of the type of the state *)
set vr := fold_varied k (AVar (pa q)) bA.
have Hvr' : vr = true by rewrite /vr /fold_varied /= Hvq.
have Hstates : forall jn, (jn <= N)%nat -> has_type (Array z) (st jn).
  elim=> [| jn IH] Hjn.
    have [_ [_ [_ [_ [_ [_ [_ [_ [Hhtq _]]]]]]]]] := static_in _ _ _ HL HqL.
    by rewrite /st Hst0 -Eqz.
  have Hjn' : (jn <= N)%nat by lia.
  have Hlt : (jn < count l h)%nat by rewrite -/N; lia.
  have Hs1 := Hstep jn Hlt.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  set ix := PV (fresh k) (VInfo k Integer None)
    (open_index (DBound (0%nat, 0%nat))) (VInt (l + Z.of_nat jn)) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
    (TVar (DBound (0%nat, 0%nat)) (Array z) None vr vr vr false None)
    (nth jn tr dflt) 0.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate;
      last by rewrite Hvr'.
    by rewrite -Ej; apply: IH.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp.
    by apply: (static_mono k) => //; lia.
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx))
      (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok) by exact: HtB.
  have [Hht _] := nbody_act _ _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP
    (PArray ix sx) (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx))
    (bD (pd ix) (pd sx)) (Array z) (st (S jn))
    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB' Hs1.
  exact: Hht.
(* a recorded state: the step ends with a set, and the loop records *)
have Hlive_abody : state_live cv k (AVar (pa q)) bA = true ->
    live = true /\ forall x y, pa x = AV k false -> pa y = AV (S k) vr ->
    abody (bP x y).
  move=> Esl.
  have Hset : aset_tail (S (S k)) (bA (AV k false) (AV (S k) vr)) = true.
    exact: (nbody_live_set L k bP bA bW (AVar (pa q)) z wP Hab HbA HbW HidL
      HkL HtB Hrai Esl).
  have Habs : forall x y, pa x = AV k false -> pa y = AV (S k) vr ->
      abody (bP x y).
    move=> x y Ex Ey.
    apply: (nbody_abody y (bP x y) (Hab x y) _ (S (S k)) (bA (pa x) (pa y))
      (HbA x _ y _)).
    by rewrite Ex Ey.
  split=> //.
  set ox := PV (AV k false) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
  set oy := PV (AV (S k) vr) (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
  rewrite /live /fold_live /fold_binders -/vr.
  rewrite (tail_fold_live_abody cv _ (Habs ox oy erefl erefl)
    (oy :: ox :: L) _ _ (HbA ox (pa ox) oy (pa oy))).
  exact: Esl.
(* an unrecorded state: the liveness of the step is the one of the loop *)
have Etl_live : state_live cv k (AVar (pa q)) bA = false ->
    tail_live cv (S (S k)) (bA (AV k false) (AV (S k) vr)) = live.
  move=> Esl; rewrite /tail_live /live /fold_live /fold_binders -/vr.
  by case: (tail_fold_live _ _ _) => // ; rewrite Esl.
(* the variables of the steps *)
have Hjq : pn q = j by move: Hst; rewrite /n /stored => -[].
have Hst_p : forall p, In p L -> stored p = DBound (pn p, pn p) by [].
have Hsn_L : forall p, In p L -> pn p <> pn q -> stored p <> n.
  by move=> p Hp Hpn; rewrite Hst_p // /n => -[E _]; apply: Hpn; rewrite Hjq.
have Hlive_b : forall p, In p L ->
    live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
      p ->
    live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p
    /\ pn p <> pn q.
  move=> p Hp Hl.
  have Ec := live_cont2 L k bP bW (pfresh k) (pfresh (S k))
    (VInfo k Integer None) (VInfo (S k) (Array z) None) (vid (pw p)) HbW HL
    erefl erefl erefl erefl.
  have Hl' : live_value k
      (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
    by move: Hl; rewrite /live_anf /live_value /= Ec => ->;
      rewrite !orb_true_r.
  split=> // E.
  case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp E) => [Epq | //].
  by move: Hl; rewrite /live_anf Ec Epq Hocc.
have Hreads_L : forall p, In p L ->
    tbr cv Replay (S (S k)) (bA (AV k false) (AV (S k) vr)) p ->
    vreads cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
  move=> p Hp; have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
  rewrite /tbr /vreads; cbn [value_needs fold_binders].
  case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
  rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
    by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
have Hflows_L : forall p, In p L ->
    useful cv Replay (S (S k)) (bA (AV k false) (AV (S k) vr)) p ->
    vflows cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
  move=> p Hp; have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
  rewrite /useful /vflows; cbn [value_needs fold_binders].
  case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
  rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
    by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
(* the loop: P jn s, the store before the step jn of the reverse loop *)
set i := DBound (c, c).
set pop := if state_live cv k (AVar (pa q)) bA then _ else [].
set body := (pop ++ fb ++ rb)%list.
set P := fun (jn : nat) (s : store R) =>
  (forall v, below c v -> consistent v -> is_primal v -> v <> n ->
     store_get s (keyv v) = store_get s2 (keyv v)) /\
  tkeep c (Some n) s2 s /\
  rev_frame_x c (inplace wP pp) n (oset O n (tangent ve)) s2 s /\
  (live = true -> store_get s (keyv (TapeOf n)) =
     Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))) /\
  store_get s (keyv n) =
    (if live then Some (primal (st jn)) else store_get s2 (keyv n)) /\
  (forall t m, In (t, m) (oset O n (tangent (st jn))) -> shaped t (barv s m)) /\
  pairing (oset O n (tangent (st jn))) s = pairing (oset O n (tangent ve)) s2.
have Ci : consistent i by [].
have Cn : consistent n by [].
have Ctn : consistent (TapeOf n) by [].
have Kti : keyv (TapeOf n) <> keyv i by rewrite /keyv.
have Ktn : keyv (TapeOf n) <> keyv n by rewrite /keyv.
have Kin : keyv i <> keyv n by rewrite /keyv /=; case=> E; lia.
have Kni : keyv n <> keyv i by apply: not_eq_sym.
have Kvi : forall v, below c v -> consistent v -> keyv v <> keyv i.
  by move=> v Hb Cv K; move: Hb; rewrite (keyv_inj _ _ Cv Ci K) /=; lia.
have Bn : below (S c) n by rewrite /=; lia.
have Btn : below (S c) (TapeOf n) by rewrite /=; lia.
have Hstep' : forall jn s, (jn < N)%nat -> P (S jn) s ->
    exists s', run body (store_set s (KVar (out_dvar nat i))
      (VInt (l + Z.of_nat jn))) = Some s' /\ P jn s'.
  move=> jn s Hjn [K0 [T0 [F0 [Tp0 [N0 [Sh0 Pr0]]]]]].
  set zz := (l + Z.of_nat jn)%Z.
  set s'' := store_set s (keyv i) (VInt zz).
  change (store_set s (KVar (out_dvar nat i)) (VInt zz)) with s''.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  have Hs1 := Hstep jn Hjn.
  have Ht0 : has_type (Array z) (nth jn tr dflt).
    by rewrite -Ej; apply: Hstates; lia.
  have Ht1 : has_type (Array z) (st (S jn)) by apply: Hstates; lia.
  have Htj : has_type (Array z) (st jn) by apply: Hstates; lia.
  have [lj Elj] : exists lj, nth jn tr dflt = VArray lj.
    by move: Ht0; case: (nth jn tr dflt) => // lj _; exists lj.
  (* the index and the state of the step *)
  set ix := PV (fresh k) (VInfo k Integer None) (open_index i) (VInt zz) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None)
    (TVar n (Array z) None vr vr vr false None) (nth jn tr dflt) j.
  have Hix : static_ok (S (S k)) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; rewrite /=; auto; try lia; try discriminate;
      last by rewrite Hvr'.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp.
    by apply: (static_mono k) => //; lia.
  have Hk' : forall p, In p (sx :: ix :: L) -> (vid (pw p) < S (S k))%nat.
    move=> p [<- | [<- | Hp]] /=; try lia.
    by have [_ [Hkp _]] := static_in _ _ _ HL Hp; lia.
  have Hu' : ids_unique (sx :: ix :: L).
    move=> p p' [<- | [<- | Hp]] [<- | [<- | Hp']] E //=; move: E => /=;
      try lia;
      try (case: (static_in _ _ _ HL Hp') => _ [Hk1 _] /=; lia);
      try (case: (static_in _ _ _ HL Hp) => _ [Hk1 _] /=; lia).
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hp').
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx))
      (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok) by exact: HtB.
  have Hjt : (jn < length tr)%nat by rewrite Hlen.
  have Hfl : length (firstn jn tr) = jn by apply: firstn_length_le; lia.
  have Epush : fold_pushes bD l (firstn (S jn) tr) =
      fold_pushes bD l (firstn jn tr) ++
        body_pushes (bD (VInt zz) (nth jn tr dflt)) (nth jn tr dflt).
    by rewrite (firstn_S_nth dflt _ _ Hjt) fold_pushes_snoc Hfl -/zz.
  (* the replay of the body keeps the keys *)
  have Hrep : forall s0 s1, run fb s0 = Some s1 -> forall v, below (S c) v ->
      consistent v -> store_get s1 (keyv v) = store_get s0 (keyv v).
    move: (adj_replay_nbody sx _ (Hab ix sx) (sx :: ix :: L) (S (S k))
             (option_map (amap pt) wP) vo (bA (pa ix) (pa sx))
             (bT (pt ix) (pt sx)) (DReal "0") (S c) (HbA ix _ sx _)
             (HbT ix _ sx _)).
    lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
      have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
    by rewrite E.
  (* the context of the body *)
  set liveb := live_anf (S (S k)) (bW (pw ix) (pw sx)).
  have Hsb : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) liveb
      (Array z).
    constructor=> //.
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
    - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
      by exists y; split=> //; split=> //; right; right.
    - by rewrite /= Hvr'; repeat split; auto.
    - move=> o p [<-] [<- | [<- | Hp]] Ep; [by left | by move: Ep => /=; lia |].
      by right=> Hl; case: (Hlive_b p Hp Hl) => _ Hpn; apply: Hpn; rewrite Hjq.
    - move=> p o [<- | [<- | Hp]] Lp Ha Hgp [<-] //.
      case: (Hlive_b p Hp Lp) => Hl' _.
      rewrite /= -Hjq.
      exact: (s_arrays _ _ _ _ _ _ _ Hs p q Hp Hl' Ha Hgp Hown).
  set tbb := tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  (* the pop: when the state is recorded, the element the step overwrote is
     restored in it, and popped from the tape *)
  have [sp [Hrp [Hsp_v [Hsp_i [Hsp_bar [Tsp [Hsp_sx Hsp_l]]]]]]] :
      exists sp, run pop s'' = Some sp /\
      (forall v, below c v -> consistent v -> ~ is_tape v -> v <> n ->
         store_get sp (keyv v) = store_get s (keyv v)) /\
      store_get sp (keyv i) = Some (VInt zz) /\
      (forall v, is_bar v -> store_get sp (keyv v) = store_get s (keyv v)) /\
      tkeep c (Some n) s sp /\
      (tbb sx -> store_get sp (keyv (stored sx)) = Some (primal (pd sx))) /\
      if state_live cv k (AVar (pa q)) bA then
        store_get sp (keyv n) = Some (primal (st jn)) /\
        store_get sp (keyv (TapeOf n)) =
          Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))
      else sp = s''.
    have Hsv : forall v, below c v -> consistent v ->
        store_get s'' (keyv v) = store_get s (keyv v).
      move=> v Hb Cv.
      have Kiv : keyv i <> keyv v by apply: not_eq_sym; apply: Kvi.
      by rewrite /s'' store_get_set_other.
    have Hsbar : forall v, is_bar v ->
        store_get s'' (keyv v) = store_get s (keyv v).
      move=> v Bv.
      have Ki1 : keyv i <> keyv v.
        by apply: not_eq_sym; apply: keyv_bar_other.
      by rewrite /s'' store_get_set_other.
    rewrite /pop; case Esl: (state_live cv k (AVar (pa q)) bA); last first.
      exists s''; split=> //; split; first by move=> v Hb Cv _ _; exact: Hsv.
      split; first by rewrite /s'' store_get_set_same.
      split; first exact: Hsbar.
      split; first exact: tkeep_set.
      split=> // Ht.
      have Hsl : tbb sx -> state_live cv k (AVar (pa q)) bA = true by [].
      by move: (Hsl Ht); rewrite Esl.
    have [Elive Habs] := Hlive_abody Esl.
    (* the step changes the array only at the index of its set *)
    have [zi [l1 [x [Hsi [Ev1 [Hx [Hback Hse]]]]]]] :=
      abody_eval_array _ (Habs ix sx erefl erefl) (sx :: ix :: L) (S (S k))
        wP ix sx _ _ (Array z) _ lj Hk' Hu' (or_introl erefl)
        (HbW ix _ sx _) (HbD ix _ sx _) HtB' Hs1 Elj.
    (* the index of the pop *)
    have [iP [Hi [Hti Hsi']]] :=
      tail_index_abody _ (Habs ix sx erefl erefl) (sx :: ix :: L) (S (S k))
        wP ix sx _ (bT (pt ix) (pt sx)) _
        (annotate_body_t cv Replay (S (S k)) (bA (pa ix) (pa sx))) (Array z)
        _ Hk' Hu' (or_intror (or_introl erefl)) (HbW ix _ sx _)
        (HbT ix _ sx _) (HbD ix _ sx _) HtB' Hs1.
    have HiD : aeval_atom (duals reals) (amap pd iP) = Some (VInt zi).
      move: Hsi'; rewrite Hsi.
      by case: (aeval_atom _ _) => [[| z1 | | |] |] // [<-].
    have Hidx : forall s0, store_get s0 (keyv i) = Some (VInt zz) ->
        xev s0 (spell (amap pt iP)) = Some (VInt zi).
      move=> s0 Hs0i.
      apply: (aspell_ok (S (S k)) s0 iP (VInt zi)) => // p E.
      by case: Hi E => [-> [<-] | [z1 ->]] //; split.
    have Hsi2 : set_index (bD (VInt zz) (nth jn tr dflt)) = Some zi.
      exact: Hsi.
    have Epush' : fold_pushes bD l (firstn (S jn) tr) =
        fold_pushes bD l (firstn jn tr) ++ [x].
      rewrite Epush.
      rewrite (body_pushes_abody _ (Habs ix sx erefl erefl) (sx :: ix :: L) _
        _ (HbD ix _ sx _)).
      by rewrite Hsi2 Elj Hx.
    have Est1 : st (S jn) = VArray l1 by exact: Ev1.
    set st1 := store_set s'' (keyv (TapeOf n))
      (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest)).
    exists (store_set st1 (keyv n) (VArray (map dfst lj))); split.
      apply: run_pop_at.
      - by rewrite /s'' store_get_set_other // (Tp0 Elive) Epush'
          rev_app_distr.
      - rewrite store_get_set_other // /s'' store_get_set_other //.
        by rewrite N0 Elive Est1.
      - have Hg : store_get st1 (keyv i) = Some (VInt zz).
          by rewrite store_get_set_other // /s'' store_get_set_same.
        by move: (Hidx _ Hg); rewrite -Hti; exact.
      exact: Hback.
    split.
      move=> v Hb Cv Tv Hvn.
      have Kvn : keyv n <> keyv v by move=> K; apply: Hvn; apply: keyv_inj.
      have Kvt : keyv (TapeOf n) <> keyv v.
        by move=> K; apply: Tv; rewrite -(keyv_inj _ _ Ctn Cv K).
      rewrite store_get_set_other // store_get_set_other //.
      exact: Hsv.
    split.
      by rewrite store_get_set_other // store_get_set_other // /s''
        store_get_set_same.
    split.
      move=> v Bv.
      have Kn1 : keyv n <> keyv v.
        by apply: not_eq_sym; apply: keyv_bar_other.
      have Kt1 : keyv (TapeOf n) <> keyv v.
        by apply: not_eq_sym; apply: keyv_bar_other.
      by rewrite store_get_set_other // store_get_set_other // Hsbar.
    split.
      apply: (tkeep_trans _ _ _ s''); first by apply: tkeep_set.
      apply: (tkeep_trans _ _ _ st1); last exact: tkeep_set.
      by apply: tkeep_set_tape => //; right.
    split; first by move=> _; rewrite store_get_set_same /sx /= Elj.
    split; first by rewrite store_get_set_same Ej Elj.
    by rewrite store_get_set_other // store_get_set_same.
  (* the variables the replay reads hold their values *)
  have Hstore_L : forall p, In p L -> tbb p ->
      store_get sp (keyv (stored p)) = Some (primal (pd p)).
    move=> p Hp Htb.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p
      (HbA ix _ sx _) (HbW ix _ sx _) HL' (or_intror (or_intror Hp))
      (or_introl Htb).
    case: (Hlive_b p Hp Hl) => Hlv Hpn.
    have Hsn := Hsn_L p Hp Hpn.
    have Hbp : below c (stored p).
      by rewrite Hst_p //; exact: (s_num _ _ _ _ _ _ _ Hs _ Hp).
    have Cp : consistent (stored p) by rewrite Hst_p.
    have Tp : ~ is_tape (stored p) by rewrite Hst_p.
    have Pp : is_primal (stored p) by rewrite Hst_p.
    rewrite (Hsp_v _ Hbp Cp Tp Hsn) (K0 _ Hbp Cp Pp Hsn).
    apply: (Hrd p Hp (Hreads_L p Hp Htb) Hlv); right.
    rewrite /inplace Hown => -[Eqp]; exfalso; apply: Hsn.
    by rewrite Hst /stored Eqp.
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) sp wP (PArray ix sx) liveb
      tbb (Array z).
    constructor=> //.
    - by move=> p [<- | [<- | Hp]] //=; exact: Hbar.
    - move=> p [<- | [<- | Hp]] Htb.
      + exact: Hsp_sx.
      + by rewrite Hsp_i.
      + exact: Hstore_L.
    - move=> p [<- | [<- | Hp]] Hrc //.
      have [lt Hlt] := Htp p Hp Hrc.
      have [l' Hl'] := proj1 T0 _ _ Hlt.
      exact: (proj1 Tsp _ _ Hl').
    - by move=> o [<-] [// | Htb]; exact: Hsp_sx.
  (* the replay, then the transpose of the body *)
  have Hra : real_or_array (Array z) by [].
  have NF : forall A : Prop, Replay = Forward -> A by [].
  have Hpp : Replay = Replay -> PArray ix sx <> PTop by [].
  move: (Hasb ix sx (sx :: ix :: L) (S (S k)) (S c) sp wP
           (PArray ix sx) Replay _ _ _ _ (Array z) (st (S jn)) (DReal "0") vo
           (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx
           Hra HtB' Hs1 (NF _) (NF _) (NF _) Hpp (NF _)).
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
    have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
  rewrite E => -[_ [Hht [s1 [R1 [F1 [T1 [_ Hrv]]]]]]].
  have Ein : inplace wP (PArray ix sx) = Some n by [].
  have Hs1v : forall v, below (S c) v -> consistent v ->
      store_get s1 (keyv v) = store_get sp (keyv v).
    by move=> v; apply: Hrep.
  have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
  have On : forall t t', In (t, n) (oset O n t') -> t = t'.
    move=> t t' /in_map_iff [[a0 b0] [Eab _]]; move: Eab => /=.
    case: ifP => [_ [-> _] // | Hne [_ Ebn]].
    by move: Hne; rewrite Ebn /= Nat.eqb_refl.
  (* the owners of the transpose: the state holds the tangent of st jn *)
  set O' := oset O n (tangent (st jn)).
  have HmO : forall t m, In (t, m) O' -> exists t0, In (t0, m) O.
    move=> t m Hin.
    have : In m (map snd O).
      rewrite -(oset_snd O n (tangent (st jn))); apply/in_map_iff.
      by exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exists t0.
  have HbO : forall t m, In (t, m) O' -> exists j', m = DBound (j', j') /\
      (j' < c)%nat.
    by move=> t m /HmO [t0 Ho1]; exact: (r_below _ _ _ _ _ _ _ Hr t0 m Ho1).
  have Hbar1 : forall t m, In (t, m) O' -> barv s1 m = barv s m.
    move=> t m Hin; have [j' [Em Hj']] := HbO t m Hin.
    have Bb : below (S c) (BarOf m) by rewrite Em /=; lia.
    have Cb : consistent (BarOf m) by rewrite Em.
    by rewrite /barv (Hs1v _ Bb Cb) Hsp_bar.
  have Hshape1 : forall t m, In (t, m) O' -> shaped t (barv s1 m).
    move=> t m Hin; rewrite (Hbar1 _ _ Hin).
    have [j' [Em _]] := HbO t m Hin.
    have Cm : consistent m by rewrite Em.
    case: (dvar_eq_dec_c m n) => [Emn | Hne].
      move: Hin; rewrite Emn => Hin; rewrite (On _ _ Hin).
      have Hin' := oset_in _ _ (tangent (st (S jn))) Hok Cn HnO.
      exact: (shaped_array_same z (st (S jn)) (st jn) _ Ht1 Htj
        (Sh0 _ _ Hin')).
    case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
      by apply: Sh0; apply: oset_other.
    by case: Hne; move/(dvar_eq_consistent n m Cn Cm): Ee.
  set use := useful cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  have Huse_L : forall p, In p L -> use p ->
      vflows cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p
      /\ stored p <> n.
    move=> p Hp Hu.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p
      (HbA ix _ sx _) (HbW ix _ sx _) HL' (or_intror (or_intror Hp))
      (or_intror Hu).
    case: (Hlive_b p Hp Hl) => _ Hpn.
    by split; [exact: Hflows_L | exact: Hsn_L].
  have Hr1 : rctx (sx :: ix :: L) (S c) wP (PArray ix sx) O' use s1.
    constructor.
    - by rewrite /O' oset_snd; exact: (r_nodup _ _ _ _ _ _ _ Hr).
    - exact: Hshape1.
    - move=> t m Hin; have [j' [-> Hj']] := HbO t m Hin.
      by exists j'; split=> //; lia.
    - move=> p [<- | [<- | Hp]] Hu Hva.
      + by rewrite /O' Ej; apply: oset_in.
      + by move: Hva.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        apply: oset_other => //.
        exact: (r_useful _ _ _ _ _ _ _ Hr p Hp Hvf Hva).
    - move=> p t [<- | [<- | Hp]] Hu Hin.
      + by rewrite (On _ _ Hin) Ej.
      + by have [j' [[Ec _] Hj']] := HbO _ _ Hin; lia.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
          exact: (r_value _ _ _ _ _ _ _ Hr p t Hp Hvf Ho1).
        have Cp : consistent (stored p) by rewrite Hst_p.
        by case: Hsn; move/(dvar_eq_consistent n _ Cn Cp): Ee.
    - by move=> o [<-]; rewrite /O' Ej; apply: oset_in.
    - move=> p ny r [<- | [<- | Hp]] //.
      exact: (r_args _ _ _ _ _ _ _ Hr p ny r Hp).
    - exact: (r_written _ _ _ _ _ _ _ Hr).
  have Hseed : seed_ok (S c) (Array z) (DReal "0") s1 by split=> // x0 [].
  have Htp1 : tapes_ok (sx :: ix :: L) s1.
    move=> p [<- | [<- | Hp]] Hrc //.
    have [lt Hlt] := Htp p Hp Hrc.
    have [l' Hl'] := proj1 T0 _ _ Hlt.
    have [l'' Hl''] := proj1 Tsp _ _ Hl'.
    exact: (proj1 T1 _ _ Hl'').
  (* the tail tape of the step: none for a set, the pushes of its inner fold
     otherwise *)
  have Hs1_n : store_get s1 (keyv n) = store_get sp (keyv n).
    exact: Hs1v.
  have Hs1_t : store_get s1 (keyv (TapeOf n)) =
      store_get sp (keyv (TapeOf n)) by exact: Hs1v.
  have Htt1 : forall ix0 sx0 n0, PArray ix sx = PArray ix0 sx0 ->
      Some n = Some n0 -> tail_tape cv (S (S k)) (sx :: ix :: L) (bP ix sx)
        (bA (pa ix) (pa sx)) (bD (pd ix) (pd sx)) s1 n0.
    move=> ix0 sx0 n0 _ [<-].
    case Esl: (state_live cv k (AVar (pa q)) bA) Hsp_l => Hsp_l.
      have [_ Habs] := Hlive_abody Esl.
      by apply: (tail_tape_abody cv); [exact: (Habs ix sx erefl erefl) |
        exact: HbA].
    apply: (tail_tape_nbody sx (bP ix sx) (Hab ix sx) (sx :: ix :: L)
      (S (S k)) _ _ s1 n _ (st (S jn)) (HbA ix (pa ix) sx (pa sx))
      (HbD ix (pd ix) sx (pd sx))) => //.
    - by left.
    - move=> p [<- | [<- | Hp]] // Epa; first by case: Epa => Epa; lia.
      have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
      by move: Epa => /(f_equal aid) /=; lia.
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have [Eid [Hkp _]] := static_in _ _ _ HL Hp; lia.
    - move=> Et; have El : live = true by rewrite -(Etl_live Esl).
      rewrite Hs1_n Hsp_l /s'' store_get_set_other //.
      by move: N0; rewrite El.
    move=> Et; have El : live = true by rewrite -(Etl_live Esl).
    rewrite Hs1_t Hsp_l /s'' store_get_set_other // (Tp0 El) Epush.
    by rewrite rev_app_distr -app_assoc.
  have [s3 [R3 [_ [_ [T3 [RF3 [Sh3 [Pr3 TB3]]]]]]]] :=
    Hrv s1 O' (agree_prim_refl _ _ _) Hr1 Hseed Htp1 Htt1.
  (* the reverse sweep of the step gives the state back, popping the pushes
     of its inner fold *)
  have [FN FT] : store_get s3 (keyv n) =
      (if live then Some (primal (st jn)) else store_get s2 (keyv n)) /\
    (live = true -> store_get s3 (keyv (TapeOf n)) =
      Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))).
    case Esl: (state_live cv k (AVar (pa q)) bA) Hsp_l => Hsp_l.
      have [Elive Habs] := Hlive_abody Esl.
      have Hbars : Forall bar_stmt rb.
        move: (adj_rev_bars_abody _ (Habs ix sx erefl erefl) (sx :: ix :: L)
          (annotate_body_t cv Replay (S (S k)) (bA (pa ix) (pa sx)))
          (option_map (amap pt) wP) vo (bT (pt ix) (pt sx)) (DReal "0") (S c)
          (HbT ix _ sx _)).
        lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
          have E2 : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
        by rewrite E2.
      have Hs3v := run_bars _ _ _ Hbars R3.
      case: Hsp_l => Hspn Hspt; rewrite Elive.
      split; first by rewrite (Hs3v n id) Hs1_n.
      by move=> _; rewrite (Hs3v (TapeOf n) id) Hs1_t.
    have Hs1_n' : store_get s1 (keyv n) =
        (if live then Some (primal (st (S jn))) else store_get s2 (keyv n)).
      by rewrite Hs1_n Hsp_l /s'' store_get_set_other.
    case Ets: (tail_fold_live cv (S (S k)) (bA (AV k false) (AV (S k) vr)))
      => [l0 |].
      (* an inner fold: its reverse loop pops the state back *)
      have Hn0 : tail_fold_live cv (S (S k)) (bA (AV k false)
          (AV (S k) (fold_varied k (AVar (pa q)) bA))) <> None.
        by rewrite -/vr Ets.
      have [Hts _] := tail_state_nbody L k bP bA (AVar (pa q)) Hab HbA Hvr' Hn0.
      have := TB3 (fun H => H) I sx erefl; rewrite Hts -/live.
      case El: live => TB; last by split=> //; rewrite TB Hs1_n' El.
      case: TB => TBn TBt.
      split; first by rewrite TBn Ej.
      move=> _; apply: TBt.
      rewrite Hs1_t Hsp_l /s'' store_get_set_other // (Tp0 El) Epush.
      by rewrite rev_app_distr -app_assoc.
    (* no inner fold: the reverse sweep writes only adjoints *)
    have El : live = false.
      by rewrite /live /fold_live /fold_binders -/vr Ets Esl.
    have Hbars : Forall bar_stmt rb.
      move: (adj_rev_bars_nbody sx (bP ix sx) (Hab ix sx) (sx :: ix :: L)
        (S (S k)) (bA (pa ix) (pa sx))
        (annotate_body_t cv Replay (S (S k)) (bA (pa ix) (pa sx)))
        (option_map (amap pt) wP) vo (bT (pt ix) (pt sx)) (DReal "0") (S c)
        (HbA ix _ sx _) Ets (HbT ix _ sx _)).
      lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
        have E2 : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
      by rewrite E2.
    rewrite El; split=> //.
    by rewrite (run_bars _ _ _ Hbars R3 n id) Hs1_n' El.
  have Hpb : forall v, is_primal v -> ~ is_bar v /\ ~ is_tape v.
    by case=> * //; split.
  (* the invariant one step down *)
  exists s3; split.
    by rewrite /body run_app Hrp run_app R1 R3.
  split.
    move=> v Hb Cv Pv Hvn; have [Bv Tv] := Hpb v Pv.
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (RF3 v Hb' Cv Tv); last first.
    - by rewrite Hs1v // Hsp_v // K0.
    - by move=> m Em; move: Pv; rewrite Em.
    by rewrite Ein => -[Env]; apply: Hvn; rewrite Env.
  split.
    apply: (tkeep_trans _ _ _ s) => //; apply: (tkeep_trans _ _ _ sp) => //.
    apply: (tkeep_trans _ _ _ s1).
      by apply: (tkeep_mono _ (S c)) => //; lia.
    by apply: (tkeep_mono _ (S c)) => //; lia.
  split.
    move=> v Hvn Hb Cv Tv Hex Hbo; rewrite -(F0 v Hvn Hb Cv Tv Hex Hbo).
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (RF3 v Hb' Cv Tv); last first.
    - by rewrite Hs1v // Hsp_v.
    - by move=> m Em; rewrite /O' oset_snd; move: (Hbo m Em); rewrite oset_snd.
    by rewrite Ein => -[Ev]; apply: Hvn.
  split; first exact: FT.
  split; first exact: FN.
  split; first exact: Sh3.
  have Hbar2 : forall t m, In (t, m) (oset O n (tangent (st (S jn)))) ->
      barv s1 m = barv s m.
    move=> t m Hin.
    have : In m (map snd O').
      rewrite /O' !oset_snd -(oset_snd O n (tangent (st (S jn)))).
      by apply/in_map_iff; exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exact: (Hbar1 _ _ Ho1).
  by rewrite Pr3 Ein /= oset_oset (pairing_ext_own _ _ _ Hbar2).
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hnd := r_nodup _ _ _ _ _ _ _ Hr.
have HstN : st N = ve by rewrite /st app_nth2 Hlen // Nat.sub_diag.
have Hst0' : st 0%nat = pd q by exact: Hst0.
have Htq : has_type (Array z) (pd q) by rewrite -Hst0'; apply: Hstates; lia.
have Htve : has_type (Array z) ve by rewrite -HstN; apply: Hstates.
have Hcons : forall t m t', In (t, m) (oset O n t') -> consistent m.
  move=> t m t' Hin.
  have : In m (map snd (oset O n t')) by apply/in_map_iff; exists (t, m).
  rewrite oset_snd => /in_map_iff [[t0 m0] [/= <- Hi]].
  exact: (Hok t0 m0 Hi).
(* before the loop: the final state *)
have HP : P N s2.
  split; first by [].
  split; first exact: tkeep_refl.
  split; first by move=> *.
  split; first by move=> El; rewrite firstn_all2 ?Hlen //; exact: Htape0.
  split; first by case El: live => //; rewrite HstN; exact: Hn_live.
  split; last by rewrite HstN.
  move=> t m; rewrite HstN => Hin; have Hm := Hcons _ _ _ Hin.
  case: (oset_mem _ _ _ _ _ Hin) => [Hi | [Em ->]].
    exact: (r_shape _ _ _ _ _ _ _ Hr t m Hi).
  move/(dvar_eq_consistent n m Cn Hm): Em => <-.
  exact: (shaped_array_same z (pd q) ve _ Htq Htve
    (r_shape _ _ _ _ _ _ _ Hr _ _ HqO)).
(* the bounds of the loop, read in the store *)
have Hlh : forall aP, (aP = loP \/ aP = hiP) -> forall p, aP = AVar p ->
    static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p)).
  move=> aP HaP p E.
  have Hp : In p L by case: HaP E => -> E; [exact: HloL p E | exact: HhiL p E].
  split; first exact: (static_in _ _ _ HL Hp).
  have Hlp : live_value k
      (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
    rewrite /live_value /=.
    by case: HaP E => -> ->; rewrite /= Nat.eqb_refl /= ?orb_true_r.
  have Hvp : vreads cv k
      (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
    rewrite /vreads; cbn [value_needs fold_binders].
    case: (needs cv Replay (S (S k)) _) => [u0 l0] /=.
    rewrite !atom_member_union.
    by case: HaP E => -> ->; rewrite /= Nat.eqb_refl /= ?orb_true_r.
  apply: (Hrd p Hp Hvp Hlp).
  case: Hpl => [Epp | _]; first by left; rewrite Epp.
  right; rewrite /inplace Hown => -[Epq].
  have Hpi : vty (pw p) = Integer.
    move/andb_true_iff: Eb => [E1 E2].
    by case: HaP E => -> E; rewrite E /= in E1 E2;
      [move/ty_eqb_true: E1 | move/ty_eqb_true: E2].
  case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp (esym Epq)) => [Epq' | Hnl].
    by exfalso; subst p; rewrite Eqz in Hpi.
  by exfalso; exact: Hnl Hlp.
have Hslo := aspell_ok k s2 loP _ (Hlh loP (or_introl erefl)) Hlo.
have Hshi := aspell_ok k s2 hiP _ (Hlh hiP (or_intror erefl)) Hhi.
(* after the loop: the initial state *)
have [sf [Hex Pf]] := exec_down_loop_from (run body) (out_dvar nat i) l N P
  Hstep' N s2 (le_n N) HP.
have Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) (count l h) s2 =
    Some sf.
  case: (Nat.eq_dec N 0) => [E0 | Hn0].
    by move: Hex; rewrite -/N E0.
  have -> : (h - 1 = l + Z.of_nat N - 1)%Z.
    by rewrite /N count_nat in Hn0 |- *; lia.
  exact: Hex.
case: Pf => [K [Tk [F [Tpf [Nn [Sh Pr]]]]]].
have Eo : oset O n (tangent (pd q)) = O by apply: oset_same.
rewrite Hst0' Eo in Sh Pr.
exists sf; split.
  by rewrite (run_forback _ _ _ _ _ _ l h Hslo Hshi) Hdown.
split; first exact: K.
split; first by move=> _ _ o; rewrite Hown => -[<-]; rewrite Hvq.
split.
  move=> Hnl _ o; rewrite Hown => -[<-] _; rewrite Nn.
  case El: live; first by rewrite Hst0'.
  exact: Hn_dead Hnl El.
do 4!(split=> //).
(* in a loop body, the state before the fold is back in the storage *)
move=> Hnl _ o; rewrite Hown => -[<-]; rewrite /fold_back Hlo Hhi -/live.
split=> El; last by rewrite Nn El.
exists tr; split; first exact: Htr.
split; first by rewrite Nn El Hst0'.
move=> l0 E; rewrite (Tpf El) /=.
by move: (Htape0 El); rewrite E => -[/app_inv_head ->].
Qed.

(* The adjoint simulation of a step of an in-place loop, of any depth. *)
Lemma nbody_asim s b : nbody s b -> asim_body cv b.
Proof.
move: s b; apply: nbody_ind.
- move=> s a e b' Hop _ IH.
  case: e Hop => //= [f aP | f aP bP0 | aP iP] _.
  + apply: asim_let; [exact: afwd_op1 | | exact: inplace_straight |
      exact: act_op1 | exact: owner_op1 | exact: IH].
    apply: asim_rev_bars; [exact: arev_op1 | by apply: straight_rev_bars |
      by apply: straight_no_top | by []].
  + apply: asim_let; [exact: afwd_op2 | | exact: inplace_straight |
      exact: act_op2 | exact: owner_op2 | exact: IH].
    apply: asim_rev_bars; [exact: arev_op2 | by apply: straight_rev_bars |
      by apply: straight_no_top | by []].
  apply: asim_let; [exact: afwd_get | | exact: inplace_straight |
    exact: act_get | exact: owner_get | exact: IH].
  apply: asim_rev_bars; [exact: arev_get | by apply: straight_rev_bars |
    by apply: straight_no_top | by []].
- move=> s a aP iP vP b' Hr.
  apply: asim_let; [exact: afwd_set | | exact: inplace_straight |
    exact: act_set | exact: owner_set | by move=> x; rewrite Hr; exact:
      asim_ret].
  apply: asim_rev_bars; [exact: arev_set | by apply: straight_rev_bars |
    by apply: straight_no_top | by []].
- move=> s a fa lo hi bi b' Hbi IH Hr.
  have Hact : forall x y, act_body (bi x y).
    by move=> x y; exact: nbody_act (Hbi x y).
  case: (array_or_not s) => Ha.
    have Hq : exists q, AVar s = AVar q /\ is_array (vty (pw q)) by exists s.
    apply: asim_let.
    - exact: afwd_fold_nbody.
    - exact: arev_fold_nbody.
    - exact: inplace_fold_gen.
    - exact: act_fold_gen.
    - exact: owner_fold_gen.
    by move=> x; rewrite Hr; exact: asim_ret.
  have Hna : forall p, AVar s = AVar p -> ~ is_array (vty (pw p)).
    by move=> p [<-].
  have Hpsb : forall x y, psim_body cv (bi x y).
    by move=> x y; exact: nbody_psim (Hbi x y).
  apply: asim_let.
  - exact: afwd_fold.
  - exact: arev_fold.
  - exact: inplace_fold.
  - exact: act_fold.
  - exact: owner_fold.
  by move=> x; rewrite Hr; exact: asim_ret.
by move=> s; exact: asim_ret.
Qed.

End NBody.
