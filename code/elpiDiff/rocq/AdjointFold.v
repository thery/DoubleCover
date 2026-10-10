(* AdjointFold.v — the adjoint simulation of folds updating an array in place
   (milestone M5).

   The body of such a fold binds scalars and ends with a single set of the
   state (abody): the forward sweep runs the steps, pushing the element each
   set overwrites on the tape when the state is recorded; the reverse sweep
   pops it back before replaying and transposing the step.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect AdjointBranch.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Section Fold.
Variable cv : bool.

(* The tape of the forward sweep after one more step: the elements it
   pushes, last. *)
Lemma fold_pushes_snoc (b : val (dual R) -> val (dual R) -> anf (val (dual R)) bare) z tr st :
  fold_pushes b z (tr ++ [st]) =
  fold_pushes b z tr ++ body_pushes (b (VInt (z + Z.of_nat (length tr))) st) st.
Proof.
elim: tr z => [| st0 tr IH] z /=.
  by rewrite app_nil_r Z.add_0_r.
rewrite IH -app_assoc.
have -> : (z + 1 + Z.of_nat (length tr) = z + Z.pos (Pos.of_succ_nat (length tr)))%Z by lia.
by [].
Qed.

(* An in-place body ending with a set pushes the element the set
   overwrites. *)
Lemma body_pushes_abody (bP : anf pv bare) : abody bP ->
  forall L bD st, anf_eq (gD L) bP bD ->
  body_pushes bD st =
  match set_index bD, st with
  | Some zi, VArray l => [match nth_z zi (map dfst l) with Some x => x | None => 0%R end]
  | _, _ => []
  end.
Proof.
elim: bP => [a e c IH | x] //= Hab L bD st HD.
case: bD HD => [aD eD cD | ?] //= [HeD HcD].
case Ev: (aeval_value (duals reals) eD) => [v |] //.
set x := PV (AV 0 false) (VInfo 0 Real None) dummy_tvar v 0.
have Hc : anf_eq (gD (x :: L)) (c x) (cD v) by exact: HcD.
case: e Hab HeD => [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0 | ? ? ? | ? ? ? | ? ? ? ? ?] //= Hab HeD;
  case: eD HeD Ev => //= *; try exact: IH x (Hab x) (x :: L) _ st Hc.
move: Hc; rewrite Hab /=; case: (cD v) => // ? /= _.
by case: (aeval_atom _ _) => [[| ? | | |] |] //; case: st.
Qed.

(* A body ending with a set has no tail fold. *)
Lemma tail_fold_live_abody (bP : anf pv bare) : abody bP ->
  forall L k bA, anf_eq (gA L) bP bA -> tail_fold_live cv k bA = None.
Proof.
elim: bP => [a e c IH | x] //= Hab L k bA HA.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have Hrec : (forall y, abody (c y)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) = None.
  by move=> Hb; exact: IH x (Hb x) (x :: L) (S k) _ (HcA x _).
have Hret : (forall y, c y = ARet (AVar y)) ->
    tail_fold_live cv (S k) (cA (let_binder k eA)) = None.
  by move=> Hb; have := HcA x (let_binder k eA); rewrite Hb; case: (cA _).
clearbody x.
case: e Hab HeA => [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? ?] //= Hab HeA;
  case: eA HeA Hrec Hret => //= *; auto.
Qed.

(* So the liveness of its fold is the liveness of its state. *)
Lemma fold_live_abody L k (bP : pv -> pv -> anf pv bare) initA bA :
  (forall x y, abody (bP x y)) ->
  (forall i1 i2 s1 s2,
     anf_eq ((s1, s2) :: (i1, i2) :: gA L) (bP i1 s1) (bA i2 s2)) ->
  fold_live cv k initA bA = state_live cv k initA bA.
Proof.
move=> Hab HbA; rewrite /fold_live /fold_binders.
set i := AV k false; set sv := AV (S k) (fold_varied k initA bA).
set ix := PV i (VInfo k Integer None) dummy_tvar (VInt 0) 0.
set sx := PV sv (VInfo (S k) Integer None) dummy_tvar (VInt 0) 0.
have Hb : anf_eq (gA (sx :: ix :: L)) (bP ix sx) (bA i sv) by exact: HbA.
by rewrite (tail_fold_live_abody _ (Hab ix sx) _ (S (S k)) _ Hb).
Qed.

(* A body ending with a set has no tail fold to take a tape from. *)
Lemma tail_tape_abody (bP : anf pv bare) : abody bP ->
  forall k L s n, tail_tape cv k L bP s n.
Proof.
elim: bP => [a e c IH | x] //= Hab k L s n.
split.
  move=> _ eA eW eD HA _ _.
  by case: e Hab HA => [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? ?] //= _;
    case: eA.
move=> y.
case: e Hab => [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? ?] //= Hab;
  try exact: IH y (Hab y) _ _ _ _.
by rewrite Hab.
Qed.

(* A live fold has a live state or a live innermost fold. *)
Lemma fold_live_split k init (b : avar -> avar -> anf avar bare) :
  fold_live cv k init b = true ->
  state_live cv k init b
  || tail_live cv (S (S k)) (b (AV k false) (AV (S k) (fold_varied k init b)))
  = true.
Proof.
rewrite /fold_live /tail_live /fold_binders.
by case: (tail_fold_live _ _ _) => [l -> | ->] //; rewrite orb_true_r.
Qed.

(* Taking one more element of a list. *)
Lemma firstn_S_nth {A} (d : A) (l : list A) m : (m < length l)%nat ->
  firstn (S m) l = firstn m l ++ [nth m l d].
Proof.
elim: l m => [| x l IH] [| m] Hlt; try by move: Hlt => /=; lia.
  by [].
rewrite !firstn_cons IH //.
by move: Hlt => /=; lia.
Qed.

(* An in-place body records nothing: it binds no fold. *)
Lemma records_in_abody (bP : anf pv bare) : abody bP ->
  forall L k bA, anf_eq (gA L) bP bA -> records_in cv k bA = false.
Proof.
elim: bP => [a e c IH | x] //= Hab L k bA HA.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
set x := PV (let_binder k eA) (VInfo k Real None) dummy_tvar (VInt 0) 0.
have Hrec : (forall y, abody (c y)) -> records_in cv (S k) (cA (let_binder k eA)) = false.
  by move=> Hb; apply: (IH x (Hb x) (x :: L) (S k)); exact: HcA.
have Hlast : (forall y, c y = ARet (AVar y)) -> records_in cv (S k) (cA (let_binder k eA)) = false.
  by move=> Hb; have := HcA x (let_binder k eA); rewrite Hb; case: (cA _).
have Hre : records cv k eA = false.
  by case: eA HeA x Hrec Hlast => //; case: e Hab.
rewrite Hre /=.
case: e Hab HeA => //; intros; [apply: Hrec | apply: Hrec | apply: Hrec | apply: Hlast]; assumption.
Qed.

(* The index the reverse loop pops into (tail_index, read from the code) is
   the index the final set of the body writes (set_index, on the duals): the
   loop index or a literal, as the typing of in-place bodies requires. *)
Lemma tail_index_abody (bP : anf pv bare) : abody bP ->
  forall L k wP ix sx bW bT bD (t : ltree) te v,
  (forall p, In p L -> (vid (pw p) < k)%nat) -> ids_unique L -> In ix L ->
  anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  typecheck (option_map (amap pw) wP) (ArrayBody (AVar (pw ix)) (AVar (pw sx))) k bW = (te, Ok) ->
  aeval (duals reals) bD = Some v ->
  exists iP, (iP = AVar ix \/ exists z, iP = ANat z) /\
    tail_index W (rebuild _ bT t) = spell (amap pt iP) /\
    set_index bD = match aeval_atom (duals reals) (amap pd iP) with Some (VInt z) => Some z | _ => None end.
Proof.
elim: bP => [a e c IH | x] //= Hab L k wP ix sx bW bT bD t te v Hk Hu Hix HW HT HD Htc Hev.
case: bW HW Htc => [aW eW cW | ?] //= [HeW HcW] Htc.
case: bT HT => [aT eT cT | ?] //= [HeT HcT].
case: bD HD Hev => [aD eD cD | ?] //= [HeD HcD] Hev.
case Ev: (aeval_value (duals reals) eD) Hev => [ve|] //= Hev.
case Etv: (typecheck_value _ _ _ _ eW) Htc => [te0 d0].
case: d0 Etv => //= Etv Htc.
(* a fresh variable for the binder: probe on the code side, the value on the dual side *)
set x := PV (AV k false) (VInfo k te0 None) (probe W) ve k.
have HxL : ~ In x L by move=> Hx; have := Hk x Hx; rewrite /=; lia.
have Hk' : forall p, In p (x :: L) -> (vid (pw p) < S k)%nat.
  by move=> p [<- | Hp] /=; [lia | have := Hk p Hp; lia].
have Hu' : ids_unique (x :: L).
  move=> p p' [<- | Hp] [<- | Hp'] E //; [have := Hk p' Hp' | have := Hk p Hp | exact: Hu]; rewrite /= in E; lia.
have Hrest : forall rest, abody (c x) -> exists iP, (iP = AVar ix \/ exists z, iP = ANat z) /\
    tail_index W (rebuild _ (cT (probe W)) rest) = spell (amap pt iP) /\
    set_index (cD ve) = match aeval_atom (duals reals) (amap pd iP) with Some (VInt z) => Some z | _ => None end.
  by move=> rest Hb; apply: (IH x Hb (x :: L) (S k) wP ix sx _ _ _ rest te v Hk' Hu' (or_intror Hix) (HcW x _) (HcT x _) (HcD x _) Htc Hev).
case: e Hab HeW HeT HeD Ev Etv => //.
(* a scalar let: the index is the one of the rest of the body *)
- move=> f0 a0 Hab' _ HeT HeD _ _.
  have [iP [Hi [Ht Hs]]] := Hrest (match t with TLet _ _ r => r | TRet => TRet end) (Hab' x).
  exists iP; split=> //; split; first by case: eT HeT => // *; case: t Ht.
  by case: eD HeD => // *.
- move=> f0 a0 b0 Hab' _ HeT HeD _ _.
  have [iP [Hi [Ht Hs]]] := Hrest (match t with TLet _ _ r => r | TRet => TRet end) (Hab' x).
  exists iP; split=> //; split; first by case: eT HeT => // *; case: t Ht.
  by case: eD HeD => // *.
- move=> a0 i0 Hab' _ HeT HeD _ _.
  have [iP [Hi [Ht Hs]]] := Hrest (match t with TLet _ _ r => r | TRet => TRet end) (Hab' x).
  exists iP; split=> //; split; first by case: eT HeT => // *; case: t Ht.
  by case: eD HeD => // *.
(* the final set *)
- move=> aP iP vP Hab' HeW HeT HeD Ev Etv.
  case: eW HeW Etv => // aW' iW vW [_ [HiW _]] Etv.
  case: eT HeT => // aT' iT vT [_ [HiT _]].
  case: eD HeD Ev => // aD' iD vD [_ [HiD _]] Ev.
  have [EiW HiL] := atom_graph pw L iP iW HiW.
  have [EiT _] := atom_graph pt L iP iT HiT.
  have [EiD _] := atom_graph pd L iP iD HiD.
  subst iW iT iD.
  move: Etv => /=.
  case: (of_atom aW') => // n0.
  case: ifP => // /andP [_ Eidx] _.
  have EcT : cT (probe W) = ARet (AVar (probe W)).
  { move: (HcT x (probe W)); rewrite Hab'.
    case: (cT (probe W)) => //= a' Ha'.
    case: a' Ha' => //= w [[E] | Hw]; first by rewrite E.
    case: HxL; move: Hw; rewrite /gT in_map_iff => -[p [[<- _] Hp]] //. }
  have EcD : exists a', cD ve = ARet a'.
    by move: (HcD x ve); rewrite Hab'; case: (cD ve) => //= a' _; exists a'.
  have Hi : iP = AVar ix \/ exists z, iP = ANat z.
  { move: Eidx; case: iP HiL HiT HiW HiD Ev => [p | s | z] HiL _ _ _ _ /=; last by right; exists z.
      rewrite orbF => /Nat.eqb_eq E; left; congr AVar.
      exact: (Hu p ix (HiL p erefl) Hix E).
    by []. }
  exists iP; split=> //; split.
    by case: t => [a0 vt rest|] /=; rewrite /Transform.is_tail EcT.
  by case: EcD => a' ->.
Qed.

(* A definition that runs writes only its variable. *)
Lemma run_define_inv s sa so (n : dvar W) e :
  run [DDefine so n e] s = Some sa -> exists w, sa = store_set s (keyv n) w.
Proof.
rewrite /run /=.
case: (xeval reals s (out_dexpr nat e)) => // w [<-].
by exists w.
Qed.

(* The replay of an in-place body (Replay mode) only defines fresh variables:
   its final set is not needed by the reverse sweep, so it is not replayed,
   and every variable opened before keeps its value, the array included. *)
Lemma adj_replay_abody (bP : anf pv bare) : abody bP ->
  forall L k w vo bA bT se c, anf_eq (gA L) bP bA -> anf_eq (gT L) bP bT ->
  let '((fb, _), _) := open_pairs (adj W w vo Replay (rebuild _ bT (annotate_body_t cv Replay k bA)) se) c in
  forall s s1, run fb s = Some s1 -> forall v, below c v -> consistent v -> store_get s1 (keyv v) = store_get s (keyv v).
Proof.
elim: bP => [a e cP IH | x] //= Hab L k w vo bA bT se c HA HT.
case: bA HA => [aA eA cA | ?] //= [HeA HcA].
case: bT HT => [aT eT cT | ?] //= [HeT HcT].
cbn [annotate_body_t].
case Enl: (needs cv Replay (S k) (cA (let_binder k eA))) => [u l].
have Cc : consistent (DBound (c, c) : dvar W) by [].
(* a defined variable is fresh: the variables below c keep their values *)
have Hdef : forall so e0 s0 sa v, run [DDefine so (DBound (c, c)) e0] s0 = Some sa -> below c v -> consistent v ->
    store_get sa (keyv v) = store_get s0 (keyv v).
{ move=> so e0 s0 sa v /run_define_inv [w0 ->] Hb Hcv.
  apply: store_get_set_other => K.
  by move: (keyv_inj _ _ Cc Hcv K) Hb => <- /=; lia. }
(* the rest of the body, opened at S c *)
have Hrest : (forall y, abody (cP y)) -> forall t vr,
  let '((fb', _), _) := open_pairs (adj W w vo Replay (rebuild _ (cT (open_let t (DBound (c, c)) vr false))
                           (annotate_body_t cv Replay (S k) (cA (let_binder k eA)))) se) (S c) in
  forall s s1, run fb' s = Some s1 -> forall v, below (S c) v -> consistent v -> store_get s1 (keyv v) = store_get s (keyv v).
  by move=> Hb t vr; exact: (IH (PV (let_binder k eA) (VInfo k Real None) (open_let t (DBound (c, c)) vr false) (VInt 0) 0)
                              (Hb _) (_ :: L) (S k) w vo _ _ se (S c) (HcA _ _) (HcT _ _)).
case: e Hab HeA HeT => // [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0] Hab HeA HeT.
(* a scalar let: the replay defines its binder, if needed, then replays the rest *)
- case: eA HeA Enl HcA Hrest => // f1 a1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // f2 a2 _ HcT Hrest.
  have := Hrest Hab (type_of (AOp1 f2 a2)) (varied_value k (AOp1 f1 a1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
- case: eA HeA Enl HcA Hrest => // f1 a1 b1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // f2 a2 b2 _ HcT Hrest.
  have := Hrest Hab (type_of (AOp2 f2 a2 b2)) (varied_value k (AOp2 f1 a1 b1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
- case: eA HeA Enl HcA Hrest => // a1 i1 _ Enl HcA Hrest; case: eT HeT HcT Hrest => // a2 i2 _ HcT Hrest.
  have := Hrest Hab (type_of (AGet a2 i2)) (varied_value k (AGet a1 i1)).
  cbn [adj let_ann rebuild_value annotate_value_t with_storage open_pairs]; rewrite !open_pairs_sbind.
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] IHr.
  case: (_ || false); cbn [open_pairs fwd_value]; case: (_ && _); cbn [open_pairs]; move=> s0 s1 Hrun v Hb Hcv.
  1-4: move: Hrun; rewrite run_app; case Er: (run _ s0) => [sa|] // Hrun.
  1-4: rewrite (IHr _ _ Hrun v (below_mono c (S c) v Hb (Nat.le_succ_diag_r c)) Hcv).
  1-2: exact: (Hdef _ _ _ _ _ Er).
  1-2: by move: Er; rewrite /run /= => -[<-].
(* the final set: the reverse sweep does not read it (needs of a return in
   Replay is empty), so it is not replayed *)
- case: eA HeA Enl HcA Hrest => // a1 i1 v1 _ Enl HcA _; case: eT HeT HcT => // a2 i2 v2 _ HcT.
  have El : l = [].
  { have := HcA (PV (let_binder k (ASet a1 i1 v1)) (VInfo k Real None) dummy_tvar (VInt 0) 0) (let_binder k (ASet a1 i1 v1)).
    rewrite Hab; move: Enl; case: (cA _) => //= r [_ <-] _; reflexivity. }
  rewrite El /=.
  have EcT : forall y, exists r, cT y = ARet r.
    by move=> y; have := HcT (PV (AV k false) (VInfo k Real None) y (VInt 0) 0) y; rewrite Hab; case: (cT y) => //= r _; exists r.
  case: a2 => [a3 | s3 | z3] /=.
  all: cbn [open_pairs]; rewrite ?open_pairs_sbind.
  + case: (EcT (open_let (tty a3) (tstored a3) (varied a1 || varied v1) (trecorded a3))) => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
  + case: (EcT (open_let Real (DBound (c, c)) (varied a1 || varied v1) false)) => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
  + case: (EcT (open_let Integer (DBound (c, c)) (varied a1 || varied v1) false)) => r ->.
    cbn [rebuild adj sweep_eqb open_pairs]; case: (_ && _); cbn [open_pairs];
    by move=> s0 s1; rewrite /run /= => -[<-].
Qed.

(* The reverse code of an in-place body writes only adjoints: the values
   of the variables, the array included, survive it. *)
Lemma adj_rev_bars_abody (bP : anf pv bare) : abody bP ->
  forall L (t : ltree) w vo bT se c, anf_eq (gT L) bP bT ->
  Forall bar_stmt (snd (fst (open_pairs (adj W w vo Replay (rebuild _ bT t) se) c))).
Proof.
elim: bP => [a e cP IH | x] // Hab L t w vo bT se c HT; rewrite /= in Hab.
case: bT HT => [aT eT cT | ?] // [HeT HcT].
have [aa [vt [rest ->]]] : exists aa vt rest,
    rebuild _ (ALet aT eT cT) t = ALet aa (rebuild_value _ eT vt) (fun v => rebuild _ (cT v) rest).
  by case: t => [aa vt rest|]; [exists aa, vt, rest | exists no_ann, TLeaf, TRet].
have Hbd : forall t0 (m : dvar W), Forall bar_stmt (bar_declaration W t0 m) by case=> * //=; do 2 constructor.
case: e Hab HeT => // [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0] Hab HeT.
- case: eT HeT HcT => // f2 a2 HeT HcT.
  cbn [rebuild_value adj with_storage]; case: (let_ann aa) => [[vv ac] cc]; cbn [open_pairs]; rewrite !open_pairs_sbind.
  set x := PV (AV 0 false) (VInfo 0 Real None) (open_let (type_of (AOp1 f2 a2)) (DBound (c, c)) vv false) (VInt 0) 0.
  have := IH x (Hab x) (x :: L) rest w vo _ se (S c) (HcT x (pt x)).
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
  have Hre := straight_rev_bars (AOp1 f0 a0) I L (AOp1 f2 a2) TLeaf w vo (type_of (AOp1 f2 a2)) (DBound (c, c)) c3 HeT.
  case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
  try (apply: Forall_cons; first by []);
  rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
- case: eT HeT HcT => // f2 a2 b2 HeT HcT.
  cbn [rebuild_value adj with_storage]; case: (let_ann aa) => [[vv ac] cc]; cbn [open_pairs]; rewrite !open_pairs_sbind.
  set x := PV (AV 0 false) (VInfo 0 Real None) (open_let (type_of (AOp2 f2 a2 b2)) (DBound (c, c)) vv false) (VInt 0) 0.
  have := IH x (Hab x) (x :: L) rest w vo _ se (S c) (HcT x (pt x)).
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
  have Hre := straight_rev_bars (AOp2 f0 a0 b0) I L (AOp2 f2 a2 b2) TLeaf w vo (type_of (AOp2 f2 a2 b2)) (DBound (c, c)) c3 HeT.
  case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
  try (apply: Forall_cons; first by []);
  rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
- case: eT HeT HcT => // a2 i2 HeT HcT.
  cbn [rebuild_value adj with_storage]; case: (let_ann aa) => [[vv ac] cc]; cbn [open_pairs]; rewrite !open_pairs_sbind.
  set x := PV (AV 0 false) (VInfo 0 Real None) (open_let (type_of (AGet a2 i2)) (DBound (c, c)) vv false) (VInt 0) 0.
  have := IH x (Hab x) (x :: L) rest w vo _ se (S c) (HcT x (pt x)).
  case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
  have Hre := straight_rev_bars (AGet a0 i0) I L (AGet a2 i2) TLeaf w vo (type_of (AGet a2 i2)) (DBound (c, c)) c3 HeT.
  case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
  try (apply: Forall_cons; first by []);
  rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
- case: eT HeT HcT => // a2 i2 v2 HeT HcT.
  have Hret : forall y t0 c0, Forall bar_stmt (snd (fst (open_pairs (adj W w vo Replay (rebuild _ (cT y) t0) se) c0))).
  { move=> y t0 c0; have := HcT (PV (AV 0 false) (VInfo 0 Real None) y (VInt 0) 0) y; rewrite Hab.
    case: (cT y) => //= r _; cbn [rebuild adj sweep_eqb open_pairs snd fst].
    case: (tof r) => //; case Eb: (bar r) => [bx|] //.
    have [x0 [-> Hx]] := bar_some _ _ Eb.
    by constructor=> //; constructor. }
  have Hre := straight_rev_bars (ASet a0 i0 v0) I L (ASet a2 i2 v2) TLeaf w vo.
  cbn [rebuild_value adj]; case: (let_ann aa) => [[vv ac] cc].
  case: a2 HeT Hre => [a3 | s3 | z3] HeT Hre; cbn [with_storage open_pairs]; rewrite !open_pairs_sbind.
  + have := Hret (open_let (tty a3) (tstored a3) vv (trecorded a3)) rest c.
    case: (open_pairs _ c) => [[fb' rb'] c3] /= IHr.
    have {}Hre := Hre (tty a3) (tstored a3) c3 HeT.
    case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
    try (apply: Forall_cons; first by []);
    rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
  + have := Hret (open_let Real (DBound (c, c)) vv false) rest (S c).
    case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
    have {}Hre := Hre Real (DBound (c, c)) c3 HeT.
    case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
    try (apply: Forall_cons; first by []);
    rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
  + have := Hret (open_let Integer (DBound (c, c)) vv false) rest (S c).
    case: (open_pairs _ (S c)) => [[fb' rb'] c3] /= IHr.
    have {}Hre := Hre Integer (DBound (c, c)) c3 HeT.
    case: cc; cbn [open_pairs]; case: ac; cbn [open_pairs] => //=;
    try (apply: Forall_cons; first by []);
    rewrite ?Forall_app; repeat split; try exact: Hbd; try exact: IHr; try exact: Hre; try by [].
Qed.

(* Writing back the element a replacement overwrote restores the list. *)
Lemma replace_nth_back {A : Type} n (x y : A) l l1 :
  replace_nth n x l = Some l1 -> nth_error l n = Some y -> replace_nth n y l1 = Some l.
Proof.
elim: n l l1 => [| n IH] [| z l] l1 //= => [[<-] [->] // | ].
case E: (replace_nth n x l) => [l2|] //= [<-] Hn /=.
by rewrite (IH _ _ E Hn).
Qed.

Lemma replace_nth_z_back {A : Type} k (x y : A) l l1 :
  replace_nth_z k x l = Some l1 -> nth_z k l = Some y -> replace_nth_z k y l1 = Some l.
Proof.
rewrite /replace_nth_z /nth_z; case: (k <? 0)%Z => //.
exact: replace_nth_back.
Qed.

(* A step of an in-place body changes its array only at the index of its
   final set; writing back the element there restores the array. *)
Lemma abody_eval_array (bP : anf pv bare) : abody bP ->
  forall L k wP ix sx bW bD te v l0,
  (forall p, In p L -> (vid (pw p) < k)%nat) -> ids_unique L -> In sx L ->
  anf_eq (gW L) bP bW -> anf_eq (gD L) bP bD ->
  typecheck (option_map (amap pw) wP) (ArrayBody (AVar (pw ix)) (AVar (pw sx))) k bW = (te, Ok) ->
  aeval (duals reals) bD = Some v -> pd sx = VArray l0 ->
  exists zi l1 x, set_index bD = Some zi /\ v = VArray l1 /\
    nth_z zi (map dfst l0) = Some x /\ replace_nth_z zi x (map dfst l1) = Some (map dfst l0) /\
    same_except (Some zi) (map dfst l0) (map dfst l1).
Proof.
elim: bP => [a e c IH | x] //= Hab L k wP ix sx bW bD te v l0 Hk Hu Hsx HW HD Htc Hev Hl0.
case: bW HW Htc => [aW eW cW | ?] //= [HeW HcW] Htc.
case: bD HD Hev => [aD eD cD | ?] //= [HeD HcD] Hev.
case Ev: (aeval_value (duals reals) eD) Hev => [ve|] //= Hev.
case Etv: (typecheck_value _ _ _ _ eW) Htc => [te0 d0].
case: d0 Etv => //= Etv Htc.
set x := PV (AV k false) (VInfo k te0 None) (probe W) ve k.
have HxL : ~ In x L by move=> Hx; have := Hk x Hx; rewrite /=; lia.
have Hk' : forall p, In p (x :: L) -> (vid (pw p) < S k)%nat.
  by move=> p [<- | Hp] /=; [lia | have := Hk p Hp; lia].
have Hu' : ids_unique (x :: L).
  move=> p p' [<- | Hp] [<- | Hp'] E //; [have := Hk p' Hp' | have := Hk p Hp | exact: Hu]; rewrite /= in E; lia.
have Hrest : abody (c x) -> exists zi l1 x0, set_index (cD ve) = Some zi /\ v = VArray l1 /\
    nth_z zi (map dfst l0) = Some x0 /\ replace_nth_z zi x0 (map dfst l1) = Some (map dfst l0) /\
    same_except (Some zi) (map dfst l0) (map dfst l1).
  by move=> Hb; apply: (IH x Hb (x :: L) (S k) wP ix sx _ _ te v l0 Hk' Hu' (or_intror Hsx) (HcW x _) (HcD x _) Htc Hev Hl0).
case: e Hab HeW HeD Ev Etv => //.
- move=> f0 a0 Hab' _ HeD _ _.
  have [zi [l1 [x0 [Hs Hr]]]] := Hrest (Hab' x).
  exists zi, l1, x0; split; last exact: Hr.
  by case: eD HeD Hs.
- move=> f0 a0 b0 Hab' _ HeD _ _.
  have [zi [l1 [x0 [Hs Hr]]]] := Hrest (Hab' x).
  exists zi, l1, x0; split; last exact: Hr.
  by case: eD HeD Hs.
- move=> a0 i0 Hab' _ HeD _ _.
  have [zi [l1 [x0 [Hs Hr]]]] := Hrest (Hab' x).
  exists zi, l1, x0; split; last exact: Hr.
  by case: eD HeD Hs.
- move=> aP iP vP Hab' HeW HeD Ev Etv.
  case: eW HeW Etv => // aW' iW vW [HaW [HiW HvW]] Etv.
  case: eD HeD Ev => // aD' iD vD [HaD [HiD HvD]] Ev.
  have [EaW HaL] := atom_graph pw L aP aW' HaW.
  have [EaD _] := atom_graph pd L aP aD' HaD.
  have [EiD _] := atom_graph pd L iP iD HiD.
  have [EvD _] := atom_graph pd L vP vD HvD.
  subst aW' aD' iD vD.
  move: Etv => /=.
  case: (of_atom (amap pw aP)) => // n0.
  case: ifP => // /andP [/andP [/andP [_ Esx] _] _] _.
  have EaP : aP = AVar sx.
  { move: Esx; destruct aP as [p | ? | ?] => //= /Nat.eqb_eq E.
    by congr AVar; exact: (Hu p sx (HaL p erefl) Hsx E). }
  subst aP.
  move: Ev; rewrite /= Hl0.
  case: (aeval_atom (duals reals) (amap pd iP)) => [[| zi | | |] |] //.
  case: (aeval_atom (duals reals) (amap pd vP)) => [[y | | | |] |] //.
  case Er: (replace_nth_z zi y l0) => [l1|] //= [Eve].
  have Ecd : cD ve = ARet (AVar ve).
  { move: (HcD x ve); rewrite Hab'; case: (cD ve) => //= r.
    case: r => //= w [[<-] // | Hw].
    case: HxL; move: Hw; rewrite /gD in_map_iff => -[p [[<- _] Hp]] //. }
  move: Hev; rewrite Ecd /= => -[Ev].
  have Hm : replace_nth_z zi (dfst y) (map dfst l0) = Some (map dfst l1).
    by rewrite replace_nth_z_map Er.
  have [x0 Hx0] := replace_nth_z_nth _ _ _ _ Hm.
  exists zi, l1, x0; split=> //; split; first by rewrite -Ev -Eve.
  split=> //; split; first exact: (replace_nth_z_back _ _ _ _ _ Hm Hx0).
  exact: (replace_same_except _ _ _ _ Hm).
Qed.

(* Two arrays of the same type have the same shape of adjoint. *)
Lemma shaped_array_same z v1 v2 b :
  has_type (Array z) v1 -> has_type (Array z) v2 -> shaped (tangent v1) b -> shaped (tangent v2) b.
Proof.
case: v1 => // l1; case: v2 => // l2 /= H1 H2.
by case: b => [[] |] //= m; rewrite !length_map H1 H2.
Qed.

Lemma oset_oset O n t t' : oset (oset O n t) n t' = oset O n t'.
Proof.
elim: O => [| [t0 n0] O IH] //=.
by case E: (dvar_eq nat n n0) => /=; rewrite ?E IH.
Qed.

Lemma oset_in O n t : owners_ok O -> consistent n -> In n (map snd O) -> In (t, n) (oset O n t).
Proof.
elim: O => [| [t0 n0] O IH] //= Ho Hn [E | Hi].
- by subst n0; rewrite (proj2 (dvar_eq_consistent n n Hn Hn) erefl); left.
by right; apply: IH => // t1 m Hm; exact: (Ho t1 m (or_intror Hm)).
Qed.

Lemma oset_other O n t t' m : owners_ok O -> consistent n -> m <> n -> In (t', m) O -> In (t', m) (oset O n t).
Proof.
elim: O => [| [t0 n0] O IH] //= Ho Hn Hmn [E | Hi]; last first.
  by right; apply: IH => // t1 m1 Hm1; exact: (Ho t1 m1 (or_intror Hm1)).
case: E => E1 E2; subst t0 n0.
have Hm : consistent m by apply: (Ho t'); left.
case E: (dvar_eq nat n m); last by left.
by move/(dvar_eq_consistent n m Hn Hm): E => E; case: Hmn.
Qed.

Lemma oset_mem O n t t' m : In (t, m) (oset O n t') -> In (t, m) O \/ (dvar_eq nat n m = true /\ t = t').
Proof.
elim: O => [| [t0 n0] O IH] //= [E | Hi]; last by case: (IH Hi) => [? | ?]; [left; right | right].
case En: (dvar_eq nat n n0) E => [] [E1 E2]; subst.
- by right.
by left; left.
Qed.

(* A pop into an element of an array. *)
Lemma run_pop_at s t n ei x xs l zi l1 :
  store_get s (keyv (TapeOf t)) = Some (VTape (x :: xs)) ->
  store_get (store_set s (keyv (TapeOf t)) (VTape xs)) (keyv n) = Some (VArray l) ->
  xev (store_set s (keyv (TapeOf t)) (VTape xs)) ei = Some (VInt zi) ->
  replace_nth_z zi x l = Some l1 ->
  run [DPop (TapeOf t) (DAt (DVar n) ei)] s =
  Some (store_set (store_set s (keyv (TapeOf t)) (VTape xs)) (keyv n) (VArray l1)).
Proof.
move=> Ht Hn Hi Hr; rewrite /run /xev /keyv /= in Ht Hn Hi |- *.
by rewrite Ht /= Hn Hi Hr.
Qed.

(* The forward sweep of a fold updating an array in place: each step runs the
   body, whose set overwrites one element of the array, pushed on the tape
   first when the state is recorded. *)
Lemma afwd_fold_body a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, psim_body cv (bP x y)) -> (forall x y, act_body (bP x y)) ->
  (forall x y, ibody (bP x y)) -> asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hpsb Hactb Hibb L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD Hc Htc Htail [j [Ej Hj]] Hst Hrec Hev.
have HA0 := HA; have HW0 := HW; have HD0 := HD.
destruct eA; try contradiction; destruct eW; try contradiction; destruct eT; try contradiction; destruct eD; try contradiction.
rewrite /= in HA HW HT HD.
repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       end; subst.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ => rename H into HbA end.
match goal with H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ => rename H into HbW end.
match goal with H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ => rename H into HbT end.
match goal with H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)), _ |- _ =>
  rename H into HbD end.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
destruct init as [ia | |]; try contradiction; move/in_gA: H13 => [HqL Eia]; subst ia.
destruct init0 as [iw | |]; try contradiction; move/in_gW: H9 => [_ Eiw]; subst iw.
destruct init1 as [it | |]; try contradiction; move/in_gT: H5 => [_ Eit]; subst it.
destruct init2 as [id | |]; try contradiction; move/in_gD: H1 => [_ Eid]; subst id.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer && ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
(* the array is the one the place updates in place *)
have [Hown Etail] : owner wP pp = Some q /\ tail = true.
{ destruct pp as [| | | ix0 sx0]; destruct tail; rewrite /= in Htc; try discriminate.
  - destruct wP as [y |] eqn:Ew; rewrite /= in Htc; last by [].
    case E: (match amap pw y with AVar y0 => (vid (pw q) =? vid y0)%nat | _ => false end) Htc => // Htc.
    have [->] := unique_written_s _ _ _ _ _ _ _ _ _ Hs HqL erefl E.
    by rewrite /= Eqz.
  - case E: (vid (pw q) =? vid (pw sx0))%nat Htc => // Htc.
    have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
    by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs HqL Hsx E). }
subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q)) = true.
  by case: (in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q))) Htc.
rewrite Hin_pl in Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k)))) Htc => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP) (ArrayBody (AVar (VInfo k Integer None)) (AVar (VInfo (S k) (Array z) None)))
            (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k)))) Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => <-.
rewrite /= Eqz in Hst; set n := DBound (j, j) in Hst Hrec *.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn rr z0 =>
  (eq_refl : fwd_value W w m (AFold (FoldAnn sv live0 recs) lo hi init b) (Array z0) nn rr =
   Fresh "i" (fun i => let '(ix, sx) := open_fold sv (Array z0) nn (DBound i) ((sweep_eqb m Forward && live0) || rr) in
     sbind (prim W w m (b ix sx)) (fun '(sb, _) =>
       Done ((if sweep_eqb m Forward && is_written w init && recs then [DTape (TapeOf nn)] else []) ++
             [DFor (DBound i) (spell lo) (spell hi) sb])%list)))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
lazymatch goal with |- context [@open_pairs ?A ?t (S c)] => destruct (@open_pairs A t (S c)) as [[sb vb] c2] eqn:Hob end.
have Hc2 : (S c <= c2)%nat.
  by lazymatch type of Hob with @open_pairs _ ?t _ = _ => have := open_pairs_mono t (S c); rewrite Hob end.
cbn [open_pairs]; split; first by lia.
have [Eidq [Hkq [Hstq [Htyq [Htvq [Htdq [Htidq [Hvaq [Hhtq Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev => [[| h | | |] |] // Hev.
set vr := fold_varied k (AVar (pa q)) bA in Hob *.
set live := state_live cv k (AVar (pa q)) bA in Hob *.
set rs := sweep_eqb m Forward && live || rec in Hob *.
set recs := records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) in Hrec *.
set tl := tail_live cv (S (S k)) (bA (AV k false) (AV (S k) vr)).
have Hrl : live || tl = true -> recs = true.
  move=> /orP [Hl | Ht]; rewrite /recs /=.
    by move: Hl; rewrite /live /state_live /fold_binders => ->.
  apply/orP; right; apply/negPn/negP => /negbTE Hri.
  move: Ht; rewrite /tl /tail_live.
  case Et: (tail_fold_live _ _ _) => [lt |] // Elt.
  by have := tail_fold_live_records cv _ _ _ Et Hri; rewrite Elt.
(* at the top, the fold declares the tape of the written argument *)
have Hisw : not_in_loop pp -> is_written (option_map (amap pt) wP) (AVar (pt q)) = true.
{ move=> Hnl; have Htid := a_tid _ _ _ _ _ _ _ _ _ Hc q Hown Hnl.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hown Hnl; try discriminate; last done.
  destruct wP as [[y | |] |]; try discriminate.
  move: Hown; case: (vty (pw y)) => [| | | z0] //= [->].
  by case: (tid (pt q)) Htid => [t _ | /(_ erefl)] //=; rewrite Nat.eqb_refl. }
set dcl := sweep_eqb m Forward && is_written (option_map (amap pt) wP) (AVar (pt q)) && recs.
set s0 := if dcl then store_set s (keyv (TapeOf n)) (VTape []) else s.
have Hrun0 : run (if dcl then [DTape (TapeOf n)] else []) s = Some s0 by rewrite /s0; case: ifP.
(* the tape the steps push on: a fresh one at the top *)
have [t0 Ht0] : exists t0, sweep_eqb m Forward && (rs || tl) = true ->
    store_get s0 (keyv (TapeOf n)) = Some (VTape t0).
{ rewrite /s0; case Edcl: dcl.
    by exists [] => _; exact: store_get_set_same.
  have Hnot : m = Forward -> not_in_loop pp -> live || tl = true -> False.
    by move=> Hm Hnl Hlv; move: Edcl; rewrite /dcl Hm (Hisw Hnl) (Hrl Hlv).
  case Ers: (sweep_eqb m Forward && (rs || tl)); last by exists [].
  have [l0 Hl0] : exists l0, store_get s (keyv (TapeOf n)) = Some (VTape l0).
  { apply: Hrec; case Erc: rec; [by left | right].
    move: Ers; rewrite /rs Erc orb_false_r => Ers.
    destruct m; last by [].
    split=> //; split; first exact: Hrl.
    split; first by rewrite /= Eqz.
    by move=> Hnl; apply: (Hnot erefl Hnl). }
  by exists l0. }
have Hvat : forall aP, In aP [loP; hiP; AVar q] -> forall p, aP = AVar p ->
              vatoms k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
{ move=> aP HaP p E; rewrite /vatoms; cbn [atoms_of_value]; rewrite atom_member_union.
  have Hin3 : In (amap pa aP) [amap pa loP; amap pa hiP; AVar (pa q)].
    by case: HaP => [<- | [<- | [<- | []]]] /=; auto.
  by rewrite (atom_member_atoms (pa p) _ _ Hin3) ?E. }
have Hvatq := Hvat (AVar q) (or_intror (or_intror (or_introl erefl))) q erefl.
have Hlivq : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) q.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
(* the state is varied: the inout argument at the top, or the state of the enclosing loop *)
have Hvq : avaried (pa q) = true.
{ destruct pp as [| | | ix0 sx0]; rewrite /= in Hown; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate.
    move: Hown; case: (vty (pw y)) => [| | | z0] //= [Eyq]; subst y.
    have Hqa' : is_array (vty (pw q)) by rewrite Eqz.
    exact: (proj2 (s_top _ _ _ _ _ _ _ Hs q erefl erefl Hqa') Hlivq).
  - case: Hown => Eyq; subst sx0.
    by have [_ [_ [_ [_ [-> _]]]]] := s_place _ _ _ _ _ _ _ Hs. }
have Hvr : vr = true by rewrite /vr /fold_varied /= Hvq.
have Hn0 : store_get s (keyv n) = Some (primal (pd q)).
  by rewrite Hst; exact: (a_owner _ _ _ _ _ _ _ _ _ Hc q Hown (or_intror Hvatq)).
have Hs0n : store_get s0 (keyv n) = Some (primal (pd q)).
  by rewrite /s0; case: ifP => _ //; rewrite store_get_set_other.
have Ts0 : tkeep c (Some n) s s0.
  rewrite /s0; case: ifP => _; last exact: tkeep_refl.
  by apply: tkeep_set_tape => //; right.
have Fs0 : fwd_frame c (Some n) None s s0.
{ move=> v _ Hcv Ht _ _; rewrite /s0; case: ifP => _ //.
  apply: store_get_set_other => K.
  have Ev : v = TapeOf n by apply: keyv_inj => //.
  by subst v; apply: Ht. }
have Hrs0 : rs = true ->
    exists tp, store_get s0 (keyv (TapeOf n)) = Some (VTape tp).
{ move=> Ers; case Efr: (sweep_eqb m Forward && (rs || tl)).
    by exists t0; exact: Ht0.
  have Erc : rec = true.
    move: Efr Ers; rewrite /rs; case: (sweep_eqb m Forward) => /= Efr Ers //.
    by move: Efr; rewrite Ers /=.
  have [tp Htp] := Hrec (or_introl Erc).
  rewrite /s0; case: ifP => _; [exists []; exact: store_get_set_same | by exists tp]. }
(* each step keeps the invariant; the loop runs the steps *)
set Inv := fun (zz : Z) (s' : store R) (st : val (dual R)) (tr : list (val (dual R))) =>
  fwd_frame c (Some n) None s s' /\ tkeep c (Some n) s s' /\ store_get s' (keyv n) = Some (primal st) /\
  has_type (Array z) st /\
  (sweep_eqb m Forward && (rs || tl) = true ->
     store_get s' (keyv (TapeOf n)) = Some (VTape (rev (fold_pushes bD l tr) ++ t0))) /\
  (rs = true -> exists tp, store_get s' (keyv (TapeOf n)) = Some (VTape tp)) /\
  zz = (l + Z.of_nat (length tr))%Z.
have Hstep : forall zz s' st tr st', Inv zz s' st tr -> aeval (duals reals) (bD (VInt zz) st) = Some st' ->
               exists s'', run sb (store_set s' (KVar (out_dvar nat (DBound (c, c)))) (VInt zz)) = Some s'' /\
                           Inv (zz + 1)%Z s'' st' (tr ++ [st]).
{ move=> zz s' st tr st' [Fr [Tk [Ns [Ht [Tp [Tr Ez]]]]]] Hbd.
  set i := DBound (c, c).
  set s'' := store_set s' (keyv i) (VInt zz).
  change (store_set s' (KVar (out_dvar nat i)) (VInt zz)) with s''.
  have Ci : consistent i by [].
  have Cn : consistent n by [].
  have Ctn : consistent (TapeOf n) by [].
  have Kin : forall v, below c v -> consistent v -> keyv v <> keyv i.
    by move=> v Hb Hcv K; move: Hb; rewrite (keyv_inj _ _ Hcv Ci K) /=; lia.
  have Hbn : below c n by rewrite /n /=.
  have N'' : store_get s'' (keyv n) = Some (primal st).
    by rewrite /s'' store_get_set_other //; apply: not_eq_sym; apply: Kin.
  have T'' : store_get s'' (keyv (TapeOf n)) = store_get s' (keyv (TapeOf n)).
    by rewrite /s'' store_get_set_other // => K; move: (keyv_inj _ _ Ctn Ci K).
  (* the index and the state of the step *)
  set ix := PV (fresh k) (VInfo k Integer None) (open_index i) (VInt zz) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None) (TVar n (Array z) None vr vr vr rs None) st j.
  have Hix : static_ok (S (S k)) ix by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate.
    by rewrite Hvr.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp; apply: (static_mono k) => //; lia.
  (* the variables the body reads are not the state before the loop *)
  have Hlive_b : forall p, In p L -> live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)) p ->
                   live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p /\ pn p <> pn q.
  { move=> p Hp Hl.
    have Ec := live_cont2 L k bP bW ix sx (VInfo k Integer None) (VInfo (S k) (Array z) None) (vid (pw p)) HbW HL erefl erefl erefl erefl.
    have Hl' : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
      by move: Hl; rewrite /live_anf /live_value /= Ec => ->; rewrite !orb_true_r.
    split=> // E.
    case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp E) => [Epq | //].
    by move: Hl; rewrite /live_anf Ec Epq Hocc. }
  have Hjq : pn q = j by move: Hst; rewrite /n /stored => -[].
  set liveb := live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None)).
  have Hsb : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) liveb (Array z).
  { constructor=> //.
    - move=> p p' [<- | [<- | Hp]] [<- | [<- | Hp']] E //=; move: E => /=; try lia;
        try (case: (static_in _ _ _ HL Hp') => _ [Hk' _] /=; lia);
        try (case: (static_in _ _ _ HL Hp) => _ [Hk' _] /=; lia).
      exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hp').
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
    - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
      by exists y; split=> //; split=> //; right; right.
    - by rewrite /= Hvr; repeat split; auto.
    - move=> o p [<-] [<- | [<- | Hp]] Ep; [by left | by move: Ep => /=; lia |].
      by right=> Hl; case: (Hlive_b p Hp Hl) => _ Hpn; apply: Hpn; rewrite Hjq.
    - move=> p o [<- | [<- | Hp]] Lp Ha Hg [<-] //.
      case: (Hlive_b p Hp Lp) => Hl' _.
      by rewrite /= -Hjq; exact: (s_arrays _ _ _ _ _ _ _ Hs p q Hp Hl' Ha Hg Hown). }
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) liveb liveb (Array z).
  { constructor=> //.
    - move=> p [<- | [<- | Hp]] //=; exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
    - move=> p [<- | [<- | Hp]] Hl; first exact: N''.
        by rewrite /s'' store_get_set_same.
      case: (Hlive_b p Hp Hl) => Hl' Hpn.
      have Hbp : below c (stored p) by rewrite /stored /=; exact: (s_num _ _ _ _ _ _ _ Hs _ Hp).
      have Hpn' : Some n <> Some (stored p).
        by move=> [E]; case: Hpn; move: E; rewrite Hjq /n /stored => ->.
      rewrite /s'' store_get_set_other; first by apply: not_eq_sym; apply: Kin.
      rewrite (Fr (stored p) Hbp erefl id Hpn') //.
      exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (live_vatoms _ _ _ _ _ p HA0 HW0 HL Hp Hl')).
    - move=> p [<- | [<- | Hp]] Hr //=.
        by rewrite T''; apply: Tr.
      have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
      have [l' Hl'] := proj1 Tk _ _ Hlt.
      by exists l'; rewrite /s'' store_get_set_other // => K; move: (keyv_inj _ _ erefl Ci K).
    - by move=> o [<-] _; exact: N''. }
  (* the step runs the body *)
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx)) (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok)
    by exact: HtB.
  have Htp'' : forall o, owner wP (PArray ix sx) = Some o ->
      sweep_eqb m Forward && tail_live cv (S (S k)) (bA (pa ix) (pa sx)) = true ->
      exists tp, store_get s'' (keyv (TapeOf (stored o))) = Some (VTape tp).
    move=> o [<-] /andP [Hm Htl].
    have Efr : sweep_eqb m Forward && (rs || tl) = true.
      by rewrite Hm; apply/orP; right.
    by rewrite T''; eexists; exact: (Tp Efr).
  have Hps := Hpsb ix sx (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) m Replay
                (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bT (pt ix) (pt sx)) (bD (pd ix) (pd sx)) (Array z) st'
                (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx HtB' Hbd Htp''.
  move: Hps.
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
    have E : @open_pairs A t (S c) = ((sb, vb), c2) by exact: Hob end.
  rewrite E => -[_ [s3 [R3 [F3 [T3 [_ Ho3]]]]]].
  have [Ns3 Tp3] := Ho3 sx erefl (Hibb ix sx).
  have [Hht' _] := Hactb ix sx (sx :: ix :: L) (S (S k)) wP (PArray ix sx)
                     (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) (Array z) st'
                     (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB' Hbd.
  exists s3; split; first exact: R3.
  split.
  { move=> v Hb Hcv Htv Hex Hvo.
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (F3 v Hb' Hcv Htv Hex Hvo) /s'' store_get_set_other; first by apply: not_eq_sym; apply: Kin.
    exact: Fr. }
  split.
  { apply: (tkeep_trans _ _ _ s') => //; apply: (tkeep_trans _ _ _ s''); first by apply: tkeep_set.
    by apply: (tkeep_mono _ (S c)) => //; lia. }
  split; first exact: Ns3.
  split; first exact: Hht'.
  (* the tape gets the element the set overwrites *)
  split.
  { move=> Efr.
    rewrite (Tp3 Efr _ (etrans T'' (Tp Efr))) fold_pushes_snoc -Ez.
    by rewrite rev_app_distr -app_assoc. }
  split.
  { move=> Ers; have [tp Htp] := Tr Ers.
    exact: (proj1 T3 _ _ (etrans T'' Htp)). }
  by rewrite length_app /= Ez; lia. }
have Hinit : Inv l s0 (pd q) [].
{ split; first exact: Fs0. split; first exact: Ts0. split; first exact: Hs0n.
  split; first by rewrite -Eqz. split; first by move=> E; rewrite (Ht0 E).
  split; first exact: Hrs0. by rewrite /= Z.add_0_r. }
have [sf [tr [Hex [Htr [Fs [Ts [Ns [_ [Tps _]]]]]]]]] :=
  fold_loop (fun v w => aeval (duals reals) (bD v w)) (run sb) (out_dvar nat (DBound (c, c))) Inv Hstep
            (count l h) l s0 (pd q) [] ve Hinit Hev.
(* the bounds, read before the loop *)
have Hatoms : forall aP, In aP [loP; hiP] -> forall p, aP = AVar p ->
                In p L /\ vatoms k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
{ move=> aP HaP p E; split; last by apply: (Hvat aP) => //; case: HaP => [<- | [<- | []]] /=; auto.
  by case: HaP => [Ea | [Ea | []]]; subst aP; auto. }
have Hops := fun aP H => operand_store _ _ _ _ _ _ _ _ _ aP Hc (Hatoms aP H).
have Hb0 : forall aP, In aP [loP; hiP] -> forall zb, aeval_atom (duals reals) (amap pd aP) = Some (VInt zb) ->
             xev s0 (spell (amap pt aP)) = Some (VInt zb).
{ move=> aP HaP zb Hz; have Hsz := aspell_ok k s aP _ (Hops aP HaP) Hz.
  rewrite /s0; case: ifP => _ //; rewrite xev_set_other //.
  by apply: (avoid_tape_spell k) => p E; case: (Hops aP HaP p E). }
have Hl0 : xev s0 (spell (amap pt loP)) = Some (VInt l) by apply: Hb0 => //=; auto.
have Hh0 : xev s0 (spell (amap pt hiP)) = Some (VInt h) by apply: Hb0 => //=; auto.
exists sf; split; first by rewrite run_app Hrun0 (run_for _ _ _ _ _ _ l h Hl0 Hh0) Hex.
split; first exact: Fs. split; first exact: Ts. split; first exact: Ns.
(* at the top, the tape holds the overwritten elements, last first *)
have Hfl : fold_live cv k (AVar (pa q)) bA = true -> live || tl = true.
  exact: fold_live_split.
split.
  case=> Hm Hnl; rewrite /fold_tape Hlo Hhi.
  change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
  move=> tr'; rewrite Htr => -[<-].
  split; first by rewrite /= Eqz.
  move=> _ /Hfl Hlv; split.
    have Efr : sweep_eqb m Forward && (rs || tl) = true.
      by move: Hlv; rewrite /rs Hm /= => /orP [-> | ->]; rewrite ?orb_true_r.
    by exists t0; rewrite (Tps Efr).
  by move=> ve'; rewrite Hev => -[<-].
(* inside a loop, the steps push on the tape of the enclosing loop *)
move=> Hm Hnl _ Htid; rewrite /fold_grow Hlo Hhi.
change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
move=> tr'; rewrite Htr => -[<-] Hlv l1 Hl1.
have Hiw : is_written (option_map (amap pt) wP) (AVar (pt q)) = false.
  have Et := Htid q Hown; rewrite /is_written.
  by case: (option_map (amap pt) wP) => [[y | |] |] //=; rewrite Et.
have Hs0 : s0 = s.
  by rewrite /s0 /dcl Hiw andb_false_r.
have Efr : sweep_eqb m Forward && (rs || tl) = true.
  move: Hlv => /orP [/Hfl /orP [Hl | Ht] | Hr]; rewrite /rs Hm /=.
  - by rewrite Hl.
  - by rewrite Ht orb_true_r.
  by rewrite Hr !orb_true_r.
have Et0 : t0 = l1 by move: (Ht0 Efr); rewrite Hs0 Hl1 => -[].
by rewrite (Tps Efr) Et0.
Qed.

(* The reverse sweep of a fold updating an array in place: a loop down the
   steps; each pops the element its set overwrote back into the array (the
   state before the step), replays the scalar lets of the body and transposes
   it, the adjoint of the array staying in place. *)

Lemma afwd_fold_inplace a (loP hiP initP : atom pv)
  (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, abody (bP x y)) -> asim_fwd cv (AFold a loP hiP initP bP).
Proof.
move=> Hq Hab; apply: afwd_fold_body => // x y.
- exact: abody_psim.
- exact: abody_act.
exact: abody_ibody.
Qed.

Lemma arev_fold_inplace a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (exists q, initP = AVar q /\ is_array (vty (pw q))) ->
  (forall x y, abody (bP x y)) -> asim_rev cv (AFold a loP hiP initP bP).
Proof.
move=> [q [-> Hqa]] Hab L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr.
have HA0 := HA; have HW0 := HW; have HD0 := HD.
destruct eA; try contradiction; destruct eW; try contradiction; destruct eT; try contradiction; destruct eD; try contradiction.
rewrite /= in HA HW HT HD.
repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
       end; subst.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ => rename H into HbA end.
match goal with H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ => rename H into HbW end.
match goal with H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ => rename H into HbT end.
match goal with H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv) (s2 : val (dual R)), _ |- _ =>
  rename H into HbD end.
have HL := s_static _ _ _ _ _ _ _ Hs.
rewrite /= in Htc.
destruct init as [ia | |]; try contradiction; move/in_gA: H13 => [HqL Eia]; subst ia.
destruct init0 as [iw | |]; try contradiction; move/in_gW: H9 => [_ Eiw]; subst iw.
destruct init1 as [it | |]; try contradiction; move/in_gT: H5 => [_ Eit]; subst it.
destruct init2 as [id | |]; try contradiction; move/in_gD: H1 => [_ Eid]; subst id.
case Eb: (ty_eqb (of_atom (amap pw loP)) Integer && ty_eqb (of_atom (amap pw hiP)) Integer) Htc => // Htc.
rewrite /= in Htc.
case Eqz: (vty (pw q)) Hqa Htc => [| | | z] // _ Htc.
rewrite /= in Htc.
(* the array is the one the place updates in place *)
have [Hown Etail] : owner wP pp = Some q /\ tail = true.
{ destruct pp as [| | | ix0 sx0]; destruct tail; rewrite /= in Htc; try discriminate.
  - destruct wP as [y |] eqn:Ew; rewrite /= in Htc; last by [].
    case E: (match amap pw y with AVar y0 => (vid (pw q) =? vid y0)%nat | _ => false end) Htc => // Htc.
    have [->] := unique_written_s _ _ _ _ _ _ _ _ _ Hs HqL erefl E.
    by rewrite /= Eqz.
  - case E: (vid (pw q) =? vid (pw sx0))%nat Htc => // Htc.
    have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
    by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs HqL Hsx E). }
subst tail.
have Hin_pl : in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q)) = true.
  by case: (in_place_init (option_map (amap pw) wP) (wplace pp) true (AVar (pw q))) Htc.
rewrite Hin_pl in Htc.
case Hocc: (occurs_anf (vid (pw q)) (S (S k)) (bW (anon k) (anon (S k)))) Htc => Htc.
  by case: (varg (pw q)) Htc => [[? ?] |].
case HtB: (typecheck (option_map (amap pw) wP) (ArrayBody (AVar (VInfo k Integer None)) (AVar (VInfo (S k) (Array z) None)))
            (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))) Htc => [tb [| mm]] // Htc.
case Etb: (ty_eqb tb (Array z)) Htc => // Htc.
case: (reads_around_inner_loop (S k) (S (S k)) (bW (anon k) (anon (S k)))) Htc => // Htc.
move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => <-.
rewrite /= Eqz in Hst; set n := DBound (j, j) in Hst Hev Hvr *.
cbn [annotate_value_t rebuild_value fold_binders].
rewrite (fun w sv live0 recs lo hi init b nn z0 =>
  (eq_refl : rev_value W w vo (AFold (FoldAnn sv live0 recs) lo hi init b) (Array z0) nn =
   Fresh "i" (fun i =>
     let '(ix, sx) := open_fold sv (Array z0) nn (DBound i) false in
     sbind (adj W w vo Replay (b ix sx) (DReal "0")) (fun sw =>
       Done (rev_loop W (DBound i) (spell lo) (spell hi)
               (if live0 then [DPop (TapeOf nn) (DAt (DVar nn) (tail_index W (b ix sx)))] else []) [] sw))))).
cbn [open_pairs open_fold].
rewrite open_pairs_sbind.
lazymatch goal with |- context [@open_pairs ?A ?t (S c)] => destruct (@open_pairs A t (S c)) as [[fb rb] c2] eqn:Hob end.
have Hc2 : (S c <= c2)%nat.
  by lazymatch type of Hob with @open_pairs _ ?t _ = _ => have := open_pairs_mono t (S c); rewrite Hob end.
cbn [open_pairs]; split; first by lia.
move=> s2 O Hrd Hr Hns Htp Hft Hrec.
(* the fold updates in place the written argument q, at the top, or the state
   q of an enclosing in-place loop, ending its body *)
have Hpl : pp = PTop \/ exists ix0 sx0, pp = PArray ix0 sx0.
  case Epp: pp Hown => [| | | ix0 sx0] //= _; first by left.
  by right; exists ix0, sx0.
have {}Hft := Hft Hpl.
have Hlivq : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) q.
  by rewrite /live_value /= Nat.eqb_refl !orb_true_r.
have Hqa' : is_array (vty (pw q)) by rewrite Eqz.
have Hvq : avaried (pa q) = true.
  case: Hpl => [Epp | [ix0 [sx0 Epp]]]; move: Hown Hs; rewrite Epp.
    case Ew: wP => [[y | |] |] //= + Hs.
    case: (vty (pw y)) => // [z0] [Eyq]; subst y.
    exact: (proj2 (s_top _ _ _ _ _ _ _ Hs q erefl erefl Hqa') Hlivq).
  move=> /= [<-] Hs.
  by have [_ [_ [_ [_ [-> _]]]]] := s_place _ _ _ _ _ _ _ Hs.
have HqO : In (tangent (pd q), n) O by rewrite Hst; exact: (r_owner _ _ _ _ _ _ _ Hr q Hown).
have HnO : In n (map snd O) by apply/in_map_iff; exists (tangent (pd q), n).
have Eput : oput O n (tangent ve) = oset O n (tangent ve) by rewrite /oput; case: in_dec.
rewrite Eput.
have {}Hrec : not_in_loop pp ->
    records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) = false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Er; apply: (Hrec Hnl _ q Hown Hvq Er); rewrite /= Eqz.
(* the states of the fold *)
rewrite /= in Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) Hev => [[| l | | |] |] // Hev.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) Hev => [[| h | | |] |] // Hev.
have [tr Htr] := fold_trace_exists _ _ _ _ _ Hev.
set dflt := VReal (Dual 0 0).
have [Hlen [Hst0 Hstep]] := fold_trace_step _ _ _ _ _ _ dflt Hev Htr.
set N := count l h.
set st := fun jn => nth jn (tr ++ [ve]) dflt.
(* the array before the reverse loop: the final state if recorded, the initial one otherwise *)
set live := state_live cv k (AVar (pa q)) bA.
have Hrecs : records cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) = live.
{ set ox := PV (fresh k) (VInfo k Integer None) dummy_tvar (VInt 0) 0.
  set oy := PV (AV (S k) (fold_varied k (AVar (pa q)) bA)) (VInfo (S k) (Array z) None) dummy_tvar (VInt 0) 0.
  have Hri := records_in_abody _ (Hab ox oy) (oy :: ox :: L) (S (S k)) _ (HbA ox (pa ox) oy (pa oy)).
  rewrite /live /state_live; cbn [records fold_binders].
  by rewrite Hri orbF. }
(* the tape holds the pushes of the steps, last first, on top of the rest *)
have Hflv : fold_live cv k (AVar (pa q)) bA = live.
  exact: (fold_live_abody L k bP _ bA Hab HbA).
have [rest [Htape0 Hn_live]] : exists rest,
    (live = true -> store_get s2 (keyv (TapeOf n)) =
       Some (VTape (rev (fold_pushes bD l tr) ++ rest))) /\
    (live = true -> store_get s2 (keyv n) = Some (primal ve)).
{ move: Hft; rewrite /fold_tape Hlo Hhi.
  change (aeval_atom (duals reals) (amap pd (AVar q))) with (Some (pd q)).
  move=> /(_ tr Htr) [_ Ha].
  have Har : is_array (of_atom (AVar (pw q))) by rewrite /= Eqz.
  case El: live; last by exists [].
  have [[rest Ht] Hv] := Ha Har (etrans Hflv El).
  by exists rest; split=> _; [exact: Ht | exact: Hv ve Hev]. }
have Hn_dead : not_in_loop pp -> live = false ->
    store_get s2 (keyv n) = Some (primal (pd q)).
  by move=> Hnl Hl; apply: Hrec Hnl _; rewrite Hrecs.
(* the states of the fold are arrays of the type of the state *)
set vr := fold_varied k (AVar (pa q)) bA.
have Hvr' : vr = true by rewrite /vr /fold_varied /= Hvq.
have [Eidq [Hkq [Hstq [Htyq [Htvq [Htdq [Htidq [Hvaq [Hhtq Hzq]]]]]]]]] := static_in _ _ _ HL HqL.
have Hstates : forall jn, (jn <= N)%nat -> has_type (Array z) (st jn).
{ elim=> [| jn IH] Hjn; first by rewrite /st Hst0 -Eqz.
  have Hjn' : (jn <= N)%nat by lia.
  have Hlt : (jn < count l h)%nat by rewrite -/N; lia.
  have Hs1 := Hstep jn Hlt.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (0%nat, 0%nat))) (VInt (l + Z.of_nat jn)) 0.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None) (TVar (DBound (0%nat, 0%nat)) (Array z) None vr vr vr false None)
              (nth jn tr dflt) 0.
  have Hix : static_ok (S (S k)) ix by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate; last by rewrite Hvr'.
    by rewrite -Ej; apply: IH.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp; apply: (static_mono k) => //; lia.
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx)) (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok)
    by exact: HtB.
  have [Hht _] := abody_act _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP (PArray ix sx)
                    (bA (pa ix) (pa sx)) (bW (pw ix) (pw sx)) (bD (pd ix) (pd sx)) (Array z) (st (S jn))
                    (HbA ix _ sx _) (HbW ix _ sx _) (HbD ix _ sx _) HL' HtB' Hs1.
  exact: Hht. }
(* the loop: P jn s, the store before the step jn of the reverse loop *)
set i := DBound (c, c).
set pop := if live then _ else [].
set body := (pop ++ fb ++ rb)%list.
set P := fun (jn : nat) (s : store R) =>
  (forall v, below c v -> consistent v -> is_primal v -> v <> n -> store_get s (keyv v) = store_get s2 (keyv v)) /\
  tkeep c (Some n) s2 s /\
  rev_frame_x c (inplace wP pp) n (oset O n (tangent ve)) s2 s /\
  (live = true -> store_get s (keyv (TapeOf n)) = Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))) /\
  store_get s (keyv n) = (if live then Some (primal (st jn)) else store_get s2 (keyv n)) /\
  (forall t m, In (t, m) (oset O n (tangent (st jn))) -> shaped t (barv s m)) /\
  pairing (oset O n (tangent (st jn))) s = pairing (oset O n (tangent ve)) s2.
have Hstep' : forall jn s, (jn < N)%nat -> P (S jn) s ->
    exists s', run body (store_set s (KVar (out_dvar nat i)) (VInt (l + Z.of_nat jn))) = Some s' /\ P jn s'.
  move=> jn s Hjn [K0 [T0 [F0 [Tp0 [N0 [Sh0 Pr0]]]]]].
  set zz := (l + Z.of_nat jn)%Z.
  set s'' := store_set s (keyv i) (VInt zz).
  change (store_set s (KVar (out_dvar nat i)) (VInt zz)) with s''.
  have Ej : st jn = nth jn tr dflt by rewrite /st app_nth1 // Hlen.
  have Hs1 := Hstep jn Hjn.
  have Ht0 : has_type (Array z) (nth jn tr dflt) by rewrite -Ej; apply: Hstates; lia.
  have Ht1 : has_type (Array z) (st (S jn)) by apply: Hstates; lia.
  have [lj Elj] : exists lj, nth jn tr dflt = VArray lj.
    by move: Ht0; case: (nth jn tr dflt) => // lj _; exists lj.
  (* the index and the state of the step *)
  set ix := PV (fresh k) (VInfo k Integer None) (open_index i) (VInt zz) c.
  set sx := PV (AV (S k) vr) (VInfo (S k) (Array z) None) (TVar n (Array z) None vr vr vr false None) (nth jn tr dflt) j.
  have Hix : static_ok (S (S k)) ix by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hsx : static_ok (S (S k)) sx.
    by repeat split; rewrite /=; auto; try lia; try discriminate; last by rewrite Hvr'.
  have HL' : Forall (static_ok (S (S k))) (sx :: ix :: L).
    constructor=> //; constructor=> //; apply: Forall_impl HL => p Hp; apply: (static_mono k) => //; lia.
  have Hk' : forall p, In p (sx :: ix :: L) -> (vid (pw p) < S (S k))%nat.
    move=> p [<- | [<- | Hp]] /=; try lia.
    by have [_ [Hkp _]] := static_in _ _ _ HL Hp; lia.
  have Hu' : ids_unique (sx :: ix :: L).
    move=> p p' [<- | [<- | Hp]] [<- | [<- | Hp']] E //=; move: E => /=; try lia;
      try (case: (static_in _ _ _ HL Hp') => _ [Hk1 _] /=; lia);
      try (case: (static_in _ _ _ HL Hp) => _ [Hk1 _] /=; lia).
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hp').
  have HtB' : typecheck (option_map (amap pw) wP) (wplace (PArray ix sx)) (S (S k)) (bW (pw ix) (pw sx)) = (Array z, Ok)
    by exact: HtB.
  (* the step changes the array only at the index of its set *)
  have [zi [l1 [x [Hsi [Ev1 [Hx [Hback Hse]]]]]]] :=
    abody_eval_array _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP ix sx _ _ (Array z) _ lj Hk' Hu'
      (or_introl erefl) (HbW ix _ sx _) (HbD ix _ sx _) HtB' Hs1 Elj.
  (* the index of the pop *)
  have [iP [Hi [Hti Hsi']]] :=
    tail_index_abody _ (Hab ix sx) (sx :: ix :: L) (S (S k)) wP ix sx _ (bT (pt ix) (pt sx)) _
      (annotate_body_t cv Replay (S (S k)) (bA (pa ix) (pa sx))) (Array z) _ Hk' Hu'
      (or_intror (or_introl erefl)) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) HtB' Hs1.
  have HiD : aeval_atom (duals reals) (amap pd iP) = Some (VInt zi).
    move: Hsi'; rewrite Hsi.
    by case: (aeval_atom _ _) => [[| z1 | | |] |] // [<-].
  have Hidx : forall s0, store_get s0 (keyv i) = Some (VInt zz) -> xev s0 (spell (amap pt iP)) = Some (VInt zi).
    move=> s0 Hs0i.
    apply: (aspell_ok (S (S k)) s0 iP (VInt zi)) => // p E.
    by case: Hi E => [-> [<-] | [z1 ->]] //; split.
  (* the pop restores the element overwritten by the step *)
  have Hjt : (jn < length tr)%nat by rewrite Hlen.
  have Hfl : length (firstn jn tr) = jn by apply: firstn_length_le; lia.
  have Hsi2 : set_index (bD (VInt zz) (nth jn tr dflt)) = Some zi by exact: Hsi.
  have Epush : fold_pushes bD l (firstn (S jn) tr) = fold_pushes bD l (firstn jn tr) ++ [x].
    rewrite (firstn_S_nth dflt _ _ Hjt) fold_pushes_snoc Hfl -/zz.
    rewrite (body_pushes_abody _ (Hab ix sx) (sx :: ix :: L) _ _ (HbD ix _ sx _)).
    by rewrite Hsi2 Elj Hx.
  have Est1 : st (S jn) = VArray l1 by exact: Ev1.
  have Kti : keyv (TapeOf n) <> keyv i by rewrite /keyv.
  have Ktn : keyv (TapeOf n) <> keyv n by rewrite /keyv.
  have Kin : keyv i <> keyv n by rewrite /keyv /=; case=> E; lia.
  have [sp [Hrp Hsp]] : exists sp, run pop s'' = Some sp /\
      sp = if live then store_set (store_set s'' (keyv (TapeOf n))
        (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))) (keyv n) (VArray (map dfst lj)) else s''.
    rewrite /pop; case El: (live); last by exists s''.
    eexists; split; last by [].
    apply: run_pop_at.
    - by rewrite /s'' store_get_set_other // (Tp0 El) Epush rev_app_distr.
    - rewrite store_get_set_other // /s'' store_get_set_other //.
      by rewrite N0 El Est1.
    - have Hg : store_get (store_set s'' (keyv (TapeOf n)) (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest))) (keyv i) = Some (VInt zz).
        by rewrite store_get_set_other // /s'' store_get_set_same.
      by move: (Hidx _ Hg); rewrite -Hti; exact.
    exact: Hback.
  (* the replay of the body keeps the keys, its transpose writes adjoints *)
  have Hrep : forall s0 s1, run fb s0 = Some s1 -> forall v, below (S c) v -> consistent v ->
      store_get s1 (keyv v) = store_get s0 (keyv v).
    move: (adj_replay_abody _ (Hab ix sx) (sx :: ix :: L) (S (S k)) (option_map (amap pt) wP) vo
             (bA (pa ix) (pa sx)) (bT (pt ix) (pt sx)) (DReal "0") (S c) (HbA ix _ sx _) (HbT ix _ sx _)).
    lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
      have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
    by rewrite E.
  have Hbars : Forall bar_stmt rb.
    move: (adj_rev_bars_abody _ (Hab ix sx) (sx :: ix :: L) (annotate_body_t cv Replay (S (S k)) (bA (pa ix) (pa sx)))
             (option_map (amap pt) wP) vo (bT (pt ix) (pt sx)) (DReal "0") (S c) (HbT ix _ sx _)).
    lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
      have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
    by rewrite E.
  (* the context of the body *)
  have Hlive_b : forall p, In p L -> live_anf (S (S k)) (bW (pw ix) (pw sx)) p ->
      live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p /\ pn p <> pn q.
    move=> p Hp Hl.
    have Ec := live_cont2 L k bP bW ix sx (pw ix) (pw sx) (vid (pw p)) HbW HL erefl erefl erefl erefl.
    have Hl' : live_value k (AFold ann0 (amap pw loP) (amap pw hiP) (AVar (pw q)) bW) p.
      by move: Hl; rewrite /live_anf /live_value /= Ec => ->; rewrite !orb_true_r.
    split=> // E.
    case: (s_owner _ _ _ _ _ _ _ Hs q p Hown Hp E) => [Epq | //].
    by move: Hl; rewrite /live_anf Ec Epq Hocc.
  have Hjq : pn q = j by move: Hst; rewrite /n /stored => -[].
  set liveb := live_anf (S (S k)) (bW (pw ix) (pw sx)).
  have Hsb : sctx (sx :: ix :: L) (S (S k)) (S c) wP (PArray ix sx) liveb (Array z).
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
      by rewrite /= -Hjq; exact: (s_arrays _ _ _ _ _ _ _ Hs p q Hp Hl' Ha Hgp Hown).
  (* the store after the pop *)
  have Ci : consistent i by [].
  have Cn : consistent n by [].
  have Ctn : consistent (TapeOf n) by [].
  have Kni : keyv n <> keyv i by apply: not_eq_sym.
  have Kvi : forall v, below c v -> consistent v -> keyv v <> keyv i.
    by move=> v Hb Cv K; move: Hb; rewrite (keyv_inj _ _ Cv Ci K) /=; lia.
  have Hsp_v : forall v, below c v -> consistent v -> ~ is_tape v -> v <> n ->
      store_get sp (keyv v) = store_get s (keyv v).
    move=> v Hb Cv Tv Hvn.
    have Kvn : keyv n <> keyv v by move=> K; apply: Hvn; apply: keyv_inj.
    have Kvt : keyv (TapeOf n) <> keyv v by move=> K; apply: Tv; rewrite -(keyv_inj _ _ Ctn Cv K).
    have Kiv : keyv i <> keyv v by apply: not_eq_sym; apply: Kvi.
    rewrite Hsp; case: (live).
      by rewrite store_get_set_other // store_get_set_other // /s'' store_get_set_other.
    by rewrite /s'' store_get_set_other.
  have Hsp_n : store_get sp (keyv n) =
      (if live then Some (primal (st jn)) else store_get s2 (keyv n)).
    rewrite Hsp; case El: (live).
      by rewrite store_get_set_same Ej Elj.
    by move: N0; rewrite El /s'' store_get_set_other.
  have Hsp_t : live = true -> store_get sp (keyv (TapeOf n)) = Some (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest)).
    by move=> El; rewrite Hsp El store_get_set_other // store_get_set_same.
  have Hsp_i : store_get sp (keyv i) = Some (VInt zz).
    rewrite Hsp; case: (live); last by rewrite /s'' store_get_set_same.
    by rewrite store_get_set_other // store_get_set_other // /s'' store_get_set_same.
  have Tsp : tkeep c (Some n) s sp.
    apply: (tkeep_trans _ _ _ s''); first by apply: tkeep_set.
    rewrite Hsp; case: (live); last exact: tkeep_refl.
    apply: (tkeep_trans _ _ _ (store_set s'' (keyv (TapeOf n)) (VTape (rev (fold_pushes bD l (firstn jn tr)) ++ rest)))).
      by apply: tkeep_set_tape => //; right.
    exact: tkeep_set.
  (* the variables the replay reads hold their values *)
  set tbb := tbr cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  have Htb_sx : tbb sx -> live = true by [].
  have Hst_p : forall p, In p L -> stored p = DBound (pn p, pn p) by [].
  have Hstore_L : forall p, In p L -> tbb p -> store_get sp (keyv (stored p)) = Some (primal (pd p)).
    move=> p Hp Htb.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p (HbA ix _ sx _) (HbW ix _ sx _) HL'
                 (or_intror (or_intror Hp)) (or_introl Htb).
    case: (Hlive_b p Hp Hl) => Hlv Hpn.
    have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
    have Hvr2 : vreads cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p.
      move: Htb; rewrite /tbb /tbr /vreads; cbn [value_needs fold_binders].
      case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
      rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
        by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
    have Hsn : stored p <> n.
      by rewrite Hst_p // /n => -[E _]; apply: Hpn; rewrite Hjq.
    have Hbp : below c (stored p) by rewrite Hst_p //; exact: (s_num _ _ _ _ _ _ _ Hs _ Hp).
    have Cp : consistent (stored p) by rewrite Hst_p.
    have Tp : ~ is_tape (stored p) by rewrite Hst_p.
    have Pp : is_primal (stored p) by rewrite Hst_p.
    rewrite (Hsp_v _ Hbp Cp Tp Hsn) (K0 _ Hbp Cp Pp Hsn).
    apply: (Hrd p Hp Hvr2 Hlv); right.
    rewrite /inplace Hown => -[Eqp]; exfalso; apply: Hsn.
    by rewrite Hst /stored Eqp.
  have Hctx : actx (sx :: ix :: L) (S (S k)) (S c) sp wP (PArray ix sx) liveb tbb (Array z).
    constructor=> //.
    - by move=> p [<- | [<- | Hp]] //=; exact: Hbar.
    - move=> p [<- | [<- | Hp]] Htb.
      + by rewrite Hsp_n (Htb_sx Htb) Ej.
      + by rewrite Hsp_i.
      + exact: Hstore_L.
    - move=> p [<- | [<- | Hp]] Hrc //.
      have [lt Hlt] := Htp p Hp Hrc.
      have [l' Hl'] := proj1 T0 _ _ Hlt.
      exact: (proj1 Tsp _ _ Hl').
    - move=> o [<-] [// | Htb].
      by rewrite Hsp_n (Htb_sx Htb) Ej.
  (* the replay, then the transpose of the body *)
  have Hra : real_or_array (Array z) by [].
  have NF : forall A : Prop, Replay = Forward -> A by [].
  have Hpp : Replay = Replay -> PArray ix sx <> PTop by [].
  move: (asim_straight cv _ (abody_straight _ (Hab ix sx)) (sx :: ix :: L) (S (S k)) (S c) sp wP
           (PArray ix sx) Replay _ _ _ _ (Array z) (st (S jn)) (DReal "0") vo
           (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _) Hctx Hra HtB' Hs1
           (NF _) (NF _) (NF _) Hpp (NF _)).
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] =>
    have E : @open_pairs A t (S c) = ((fb, rb), c2) by exact: Hob end.
  rewrite E => -[_ [Hht [s1 [R1 [F1 [T1 [_ Hrv]]]]]]].
  have Ein : inplace wP (PArray ix sx) = Some n by [].
  have Hs1v : forall v, below (S c) v -> consistent v -> store_get s1 (keyv v) = store_get sp (keyv v).
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
    have : In m (map snd O) by rewrite -(oset_snd O n (tangent (st jn))); apply/in_map_iff; exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exists t0.
  have HbO : forall t m, In (t, m) O' -> exists j', m = DBound (j', j') /\ (j' < c)%nat.
    by move=> t m /HmO [t0 Ho1]; exact: (r_below _ _ _ _ _ _ _ Hr t0 m Ho1).
  have Hsp_bar : forall v, is_bar v -> store_get sp (keyv v) = store_get s (keyv v).
    move=> v Bv.
    have K1 : forall x, ~ is_bar x -> keyv x <> keyv v.
      by move=> y0 Hy0; apply: not_eq_sym; apply: keyv_bar_other.
    have Kn1 := K1 n id.
    have Kt1 := K1 (TapeOf n) id.
    have Ki1 := K1 i id.
    rewrite Hsp; case: (live); last by rewrite /s'' store_get_set_other.
    by rewrite store_get_set_other // store_get_set_other // /s'' store_get_set_other.
  have Hbar1 : forall t m, In (t, m) O' -> barv s1 m = barv s m.
    move=> t m Hin; have [j' [Em Hj']] := HbO t m Hin.
    have Bb : below (S c) (BarOf m) by rewrite Em /=; lia.
    have Cb : consistent (BarOf m) by rewrite Em.
    by rewrite /barv (Hs1v _ Bb Cb) Hsp_bar.
  have Htj : has_type (Array z) (st jn) by apply: Hstates; lia.
  have Hshape1 : forall t m, In (t, m) O' -> shaped t (barv s1 m).
    move=> t m Hin; rewrite (Hbar1 _ _ Hin).
    have [j' [Em _]] := HbO t m Hin.
    have Cm : consistent m by rewrite Em.
    case: (dvar_eq_dec_c m n) => [Emn | Hne].
      move: Hin; rewrite Emn => Hin; rewrite (On _ _ Hin).
      have Hin' := oset_in _ _ (tangent (st (S jn))) Hok Cn HnO.
      exact: (shaped_array_same z (st (S jn)) (st jn) _ Ht1 Htj (Sh0 _ _ Hin')).
    case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
      by apply: Sh0; apply: oset_other.
    by case: Hne; move/(dvar_eq_consistent n m Cn Cm): Ee.
  set use := useful cv Replay (S (S k)) (bA (pa ix) (pa sx)).
  have Huse_L : forall p, In p L -> use p ->
      vflows cv k (AFold ann (amap pa loP) (amap pa hiP) (AVar (pa q)) bA) p /\ stored p <> n.
    move=> p Hp Hu.
    have Hl := tbr_occurs cv (sx :: ix :: L) (S (S k)) _ _ _ Replay p (HbA ix _ sx _) (HbW ix _ sx _) HL'
                 (or_intror (or_intror Hp)) (or_intror Hu).
    case: (Hlive_b p Hp Hl) => _ Hpn.
    have [Eid [Hkp _]] := static_in _ _ _ HL Hp.
    split; last by rewrite Hst_p // /n => -[E0 _]; apply: Hpn; rewrite Hjq.
    move: Hu; rewrite /use /useful /vflows; cbn [value_needs fold_binders].
    case: (needs cv Replay (S (S k)) _) => [u0 l0] /= Hm.
    rewrite atom_member_union !atom_member_remove ?Hm ?orb_true_r //;
      by cbn [same_term aid]; rewrite Eid; apply Nat.eqb_neq; lia.
  have Hr1 : rctx (sx :: ix :: L) (S c) wP (PArray ix sx) O' use s1.
    constructor.
    - by rewrite /O' oset_snd; exact: (r_nodup _ _ _ _ _ _ _ Hr).
    - exact: Hshape1.
    - by move=> t m Hin; have [j' [-> Hj']] := HbO t m Hin; exists j'; split=> //; lia.
    - move=> p [<- | [<- | Hp]] Hu Hva.
      + by rewrite /O' Ej; apply: oset_in.
      + by move: Hva.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        by apply: oset_other => //; exact: (r_useful _ _ _ _ _ _ _ Hr p Hp Hvf Hva).
    - move=> p t [<- | [<- | Hp]] Hu Hin.
      + by rewrite (On _ _ Hin) Ej.
      + by have [j' [[Ec _] Hj']] := HbO _ _ Hin; lia.
      + have [Hvf Hsn] := Huse_L p Hp Hu.
        case: (oset_mem _ _ _ _ _ Hin) => [Ho1 | [Ee _]].
          exact: (r_value _ _ _ _ _ _ _ Hr p t Hp Hvf Ho1).
        have Cp : consistent (stored p) by rewrite Hst_p.
        by case: Hsn; move/(dvar_eq_consistent n _ Cn Cp): Ee.
    - by move=> o [<-]; rewrite /O' Ej; apply: oset_in.
    - by move=> p ny r [<- | [<- | Hp]] //; exact: (r_args _ _ _ _ _ _ _ Hr p ny r Hp).
    - exact: (r_written _ _ _ _ _ _ _ Hr).
  have Hseed : seed_ok (S c) (Array z) (DReal "0") s1 by split=> // x0 [].
  have Htp1 : tapes_ok (sx :: ix :: L) s1.
    move=> p [<- | [<- | Hp]] Hrc //.
    have [lt Hlt] := Htp p Hp Hrc.
    have [l' Hl'] := proj1 T0 _ _ Hlt.
    have [l'' Hl''] := proj1 Tsp _ _ Hl'.
    exact: (proj1 T1 _ _ Hl'').
  have Htt1 : forall ix0 sx0 n0, PArray ix sx = PArray ix0 sx0 ->
      Some n = Some n0 -> tail_tape cv (S (S k)) (sx :: ix :: L) (bP ix sx) s1 n0.
    by move=> ix0 sx0 n0 _ _; exact: tail_tape_abody.
  have [s3 [R3 [_ [_ [T3 [RF3 [Sh3 [Pr3 _]]]]]]]] :=
    Hrv s1 O' (agree_prim_refl _ _ _) Hr1 Hseed Htp1 Htt1.
  have Hs3v : forall v, ~ is_bar v -> store_get s3 (keyv v) = store_get s1 (keyv v).
    exact: (run_bars _ _ _ Hbars R3).
  have Hpb : forall v, is_primal v -> ~ is_bar v /\ ~ is_tape v by case=> * //; split.
  have Btn : below (S c) (TapeOf n) by rewrite /=; lia.
  have Bn : below (S c) n by rewrite /=; lia.
  (* the invariant one step down *)
  exists s3; split.
    by rewrite /body run_app Hrp run_app R1 R3.
  split.
    move=> v Hb Cv Pv Hvn; have [Bv Tv] := Hpb v Pv.
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    by rewrite Hs3v // Hs1v // Hsp_v // K0.
  split.
    apply: (tkeep_trans _ _ _ s) => //; apply: (tkeep_trans _ _ _ sp) => //.
    apply: (tkeep_trans _ _ _ s1); first by apply: (tkeep_mono _ (S c)) => //; lia.
    by apply: (tkeep_mono _ (S c)) => //; lia.
  split.
    move=> v Hvn Hb Cv Tv Hex Hbo; rewrite -(F0 v Hvn Hb Cv Tv Hex Hbo).
    have Hb' : below (S c) v by apply: (below_mono c) => //; lia.
    rewrite (RF3 v Hb' Cv Tv); last first.
    - by rewrite Hs1v // Hsp_v.
    - by move=> m Em; rewrite /O' oset_snd; move: (Hbo m Em); rewrite oset_snd.
    by rewrite Ein => -[Ev]; apply: Hvn.
  split.
    by move=> El; rewrite (Hs3v (TapeOf n) id) (Hs1v _ Btn Ctn); exact: Hsp_t.
  split.
    by rewrite (Hs3v n id) (Hs1v _ Bn Cn); exact: Hsp_n.
  split; first exact: Sh3.
  have Hbar2 : forall t m, In (t, m) (oset O n (tangent (st (S jn)))) -> barv s1 m = barv s m.
    move=> t m Hin.
    have : In m (map snd O').
      by rewrite /O' !oset_snd -(oset_snd O n (tangent (st (S jn)))); apply/in_map_iff; exists (t, m).
    by move=> /in_map_iff [[t0 m0] [/= -> Ho1]]; exact: (Hbar1 _ _ Ho1).
  by rewrite Pr3 Ein /= oset_oset (pairing_ext_own _ _ _ Hbar2).
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hnd := r_nodup _ _ _ _ _ _ _ Hr.
have Cn : consistent n by [].
have HstN : st N = ve by rewrite /st app_nth2 Hlen // Nat.sub_diag.
have Hst0' : st 0%nat = pd q by exact: Hst0.
have Htq : has_type (Array z) (pd q) by rewrite -Hst0'; apply: Hstates; lia.
have Htve : has_type (Array z) ve by rewrite -HstN; apply: Hstates.
have Hcons : forall t m t', In (t, m) (oset O n t') -> consistent m.
  move=> t m t' Hin.
  have : In m (map snd (oset O n t')) by apply/in_map_iff; exists (t, m).
  by rewrite oset_snd => /in_map_iff [[t0 m0] [/= <- Hi]]; exact: (Hok t0 m0 Hi).
(* before the loop: the final state *)
have HP : P N s2.
  split; first by [].
  split; first exact: tkeep_refl.
  split; first by move=> *.
  split; first by move=> El; rewrite firstn_all2 ?Hlen //; exact: Htape0.
  split; first by case El: live => //; rewrite HstN; exact: Hn_live.
  split; last by rewrite HstN.
  move=> t m; rewrite HstN => Hin; have Hm := Hcons _ _ _ Hin.
  case: (oset_mem _ _ _ _ _ Hin) => [Hi | [Em ->]]; first exact: (r_shape _ _ _ _ _ _ _ Hr t m Hi).
  move/(dvar_eq_consistent n m Cn Hm): Em => <-.
  exact: (shaped_array_same z (pd q) ve _ Htq Htve (r_shape _ _ _ _ _ _ _ Hr _ _ HqO)).
(* the bounds of the loop, read in the store *)
have Hlh : forall aP, (aP = loP \/ aP = hiP) -> forall p, aP = AVar p ->
    static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p)).
  move=> aP HaP p E.
  have Hp : In p L by case: HaP E => -> E; [exact: H11 p E | exact: H12 p E].
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
have [sf [Hex Pf]] := exec_down_loop_from (run body) (out_dvar nat i) l N P Hstep' N s2 (le_n N) HP.
have Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) (count l h) s2 = Some sf.
  case: (Nat.eq_dec N 0) => [E0 | Hn0].
    by move: Hex; rewrite -/N E0.
  have -> : (h - 1 = l + Z.of_nat N - 1)%Z by rewrite /N count_nat in Hn0 |- *; lia.
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
move=> Hnl _ o; rewrite Hown => -[<-]; rewrite /fold_back Hlo Hhi Hflv => El.
exists tr; split; first exact: Htr.
split; first by rewrite Nn El Hst0'.
move=> l0 E; rewrite (Tpf El) /=.
by move: (Htape0 El); rewrite E => -[/app_inv_head ->].
Qed.

End Fold.
