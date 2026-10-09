(* TangentLoops.v — theorem 1, continued: the loops of the tangent
   simulation, a map writing the output array, and the folds, on a real state
   or updating an array in place. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness TangentCorrect.

From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope R_scope.

(* The context of the body of a map or of a scalar fold: no storage updated
   in place. *)
Lemma ctx_scalar (L : list pv) k c s wP (live : pv -> Prop) :
  Forall (static_ok k) L -> ids_unique L -> (forall p, In p L -> (pn p < c)%nat) ->
  (forall p, In p L -> live p -> store_ok s p) ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L /\ varg (pw y) <> None) ->
  ctx_ok L k c s wP PScalar live Real.
Proof. by move=> *; constructor. Qed.

(* A write to a variable opened at or after c keeps the frame. *)
Lemma frame_set_fresh c ex s s' v w :
  frame c ex s s' -> ~ below c v -> consistent v -> frame c ex s (store_set s' (keyv v) w).
Proof.
move=> F Hb Hc u Hu Hcu Hex; rewrite store_get_set.
case E: (key_eqb (keyv v) (keyv u)); last exact: F.
by move/key_eqb_eq/keyv_inj: E => /(_ Hc Hcu) E; subst.
Qed.

Lemma frame_chain_same c c' ex s s0 s1 :
  frame c ex s s0 -> frame c' ex s0 s1 -> (c <= c')%nat -> frame c ex s s1.
Proof.
move=> F1 F2 Hc v Hb Hcv Hex.
by rewrite (F2 v (below_mono _ _ _ Hb Hc) Hcv Hex); apply: F1.
Qed.

Lemma count_nat lo hi : count lo hi = Z.to_nat (hi - lo).
Proof. by []. Qed.

(* A map, at the end of a function that writes an array: the loop writes
   each element of the output, and of its tangent. *)
Lemma sim_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, sim_body (bP x)) -> sim_value (AMap loP hiP bP).
Proof.
move=> IHb.
value_intro.
rewrite /= in Htc Hev *.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
have HL := c_static _ _ _ _ _ _ _ _ Hc.
(* typing: at the top, at the end, from index 0, writing an array argument *)
case: pp Hc Htc => [| | | ix0 sx0] Hc /= Htc //.
case: tail Htail Htc Hst => Htail Htc Hst //.
destruct loP as [? | ? | l0]; rewrite /= in Htc; try discriminate.
destruct hiP as [? | ? | h]; rewrite /= in Htc; try discriminate.
move: Htc; case El: (~~ (l0 =? 0)%Z) => // Htc.
move/negbFE/Z.eqb_eq: El => El; subst l0.
have Hte : te = Array (h - 0) by clear - Htc; crush_match Htc.
have Hra : is_array ty by rewrite -(Htail erefl) Hte.
case Eo: (owner wP PTop) => [o |]; last first.
  by case: (c_ty _ _ _ _ _ _ _ _ Hc Hra Eo).
destruct wP as [[o' | |] |]; rewrite /= in Eo; try discriminate.
case Ey: (vty (pw o')) Eo => [| | | ny] // [Eo]; subst o'.
rewrite /= in Hst; case: Hst => Ej _; subst j.
have [Hnocc HtB] : occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
    typecheck (Some (AVar (pw o))) ScalarBody (S k)
      (bW (VInfo k Integer None)) = (Real, Ok).
  move: Htc => /=; case: (varg (pw o)) => [[nm [] ] |] /=;
    case: (occurs_anf (vid (pw o)) (S k) (bW (anon k))) => //;
    case: (typecheck (Some (AVar (pw o))) ScalarBody (S k)
             (bW (VInfo k Integer None))) => [tb [| mm]] //=;
    by case Etb: (ty_eqb tb Real) => // _; move/ty_eqb_true: Etb => ->.
have [o'' [[Eo''] [HoL _]]] := c_written _ _ _ _ _ _ _ _ Hc _ erefl.
subst o''.
have Hia : is_array (vty (pw o)) by rewrite Ey.
have [Hty [_ [l1 [l2 [A1 [A2 [A3 A4]]]]]]] :=
  c_top _ _ _ _ _ _ _ _ Hc o erefl erefl Hia.
rewrite Ey in Hty A2 A4; rewrite -(Htail erefl) Hte in Hty.
case: Hty => Ehn; clear Htc.
(* the dual evaluation *)
rewrite /= in Hev; move: Hev.
case Hxs: (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h))
  => [xs |] // [Ev]; subst ve.
(* the body, opened *)
rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
have Hc2 : (S c <= c2)%nat.
  by rewrite -[c2]/(snd (sb, (vb, db), c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs spell amap].
set vr := varied_anf (S k) (bA (fresh k)).
set n := DBound (pn o, pn o).
set i := DBound (c, c).
set bodyst := (sb ++ [DAssign (DAt (DVar n) (DVar i)) vb;
                      DAssign (DAt (DVar (DotOf n)) (DVar i))
                        (if vr then db else DReal "0")])%list.
rewrite (_ : run _ s = run [DFor i (DInt 0) (DInt h) bodyst] s).
  by rewrite /tan_map /bodyst /vr; case: (varied_anf _ _).
have Hlen1 : length l1 = count 0 h by rewrite A2 count_nat Ehn.
have Hlen2 : length l2 = count 0 h by rewrite A4 count_nat Ehn.
have Hown : owner (Some (AVar o)) PTop = Some o by rewrite /= Ey.
(* the variables the body reads are not the output array *)
have Hlive_b : forall p, In p L ->
    live_anf (S k) (bW (VInfo k Integer None)) p ->
    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o.
  move=> p Hp Hl.
  have Hcont := live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL
                  erefl erefl.
  have Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p.
    by rewrite /live_anf /live_value /= in Hl *; rewrite -Hcont.
  split=> // E.
  have [Ep | //] := c_owner _ _ _ _ _ _ _ _ Hc o p Hown Hp E; subst p.
  by rewrite /live_anf Hcont in Hl; congruence.
pose Inv := fun (z : Z) (s' : store R) (acc : list (dual R)) =>
  z = Z.of_nat (length acc) /\ frame c (Some n) s s' /\
  store_get s' (keyv n) =
    Some (VArray (map dfst acc ++ skipn (length acc) l1))%list /\
  store_get s' (keyv (DotOf n)) =
    Some (VArray (map dsnd acc ++ skipn (length acc) l2))%list /\
  (vr = false -> Forall (fun d => dsnd d = 0) acc).
have Hloop : exists sf,
    exec_up R (run bodyst) (out_dvar nat i) 0 (count 0 h) s = Some sf /\
    Inv (0 + Z.of_nat (count 0 h))%Z sf ([] ++ xs)%list.
  have Hbnd : (0 + Z.of_nat (count 0 h) <= Z.of_nat (count 0 h))%Z by lia.
  have Hi0 : Inv 0%Z s [] by [].
  apply: (map_loop_bounded (fun v => aeval (duals reals) (bD v)) (run bodyst)
            (out_dvar nat i) Inv (Z.of_nat (count 0 h)) _ _ _ _ _ _
            Hbnd Hi0 Hxs).
  move=> z s' acc d Hz [Ez [Hfr' [Hn' [Hd' Hzero]]]] Hbd.
  set s'' := store_set s' (KVar (out_dvar nat i)) (VInt z).
  set ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c)))
              (VInt z) c.
  have Hix : static_ok (S k) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hpo : (pn o < c)%nat := c_num _ _ _ _ _ _ _ _ Hc o HoL.
  have Hctx : ctx_ok (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
                (live_anf (S k) (bW (VInfo k Integer None))) Real.
    apply: ctx_scalar.
    - constructor=> //; apply: (Forall_impl _ _ HL) => p Hp.
      by apply: (static_mono k _ p Hp); lia.
    - move=> p q [Ep | Hp] [Eq | Hq] E; subst => //;
        try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; rewrite /= in E; lia);
        try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; rewrite /= in E; lia).
      exact: (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
    - move=> p [<- /= | Hp]; first lia.
      by move: (c_num _ _ _ _ _ _ _ _ Hc _ Hp) => /=; lia.
    - move=> p [<- | Hp] Hl.
        by split; first by rewrite /s'' store_get_set_same.
      have [Hl' Hpn] := Hlive_b p Hp Hl.
      have Hpc := c_num _ _ _ _ _ _ _ _ Hc _ Hp.
      have [S1 S2] := c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl'.
      have F1 : store_get s' (keyv (stored p)) = store_get s (keyv (stored p)).
        by apply: Hfr' => //= m [<-]; split; first case.
      have F2 : store_get s' (keyv (DotOf (stored p))) =
                store_get s (keyv (DotOf (stored p))).
        by apply: Hfr' => //= m [<-]; split; last case.
      rewrite /s''; split.
        rewrite store_get_set_other; last by rewrite F1.
        by rewrite /keyv /stored /= => -[]; lia.
      by move=> Hd; rewrite store_get_set_other // F2; exact: S2.
    move=> a0 [<-]; exists o; split=> //; split; first by right.
    by have [? [[Ex] [_ Hg]]] := c_written _ _ _ _ _ _ _ _ Hc _ erefl; subst.
  have := IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar Replay
            (bA (fresh k)) (bW (VInfo k Integer None))
            (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real (VReal d)
            (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx I HtB Hbd.
  rewrite Hob => -[_ [_ [Hzb [_ [Hrvd [s3 [Hrun3 [Hfr3 [Hvb Hdb]]]]]]]]].
  move/dot_vars_res: Hrvd => Hrvd.
  (* the stored array and the index, after the body *)
  have Kin : keyv i <> keyv n by rewrite /keyv /i /n /= => -[]; lia.
  have S3n : store_get s3 (keyv n) = store_get s' (keyv n).
    rewrite (Hfr3 n) //; first by rewrite /n /=; lia.
    by rewrite /s''; apply: store_get_set_other.
  have S3d : store_get s3 (keyv (DotOf n)) = store_get s' (keyv (DotOf n)).
    rewrite (Hfr3 (DotOf n)) //; first by rewrite /n /=; lia.
    by rewrite /s''; apply: store_get_set_other.
  have S3i : xev s3 (DVar i) = Some (VInt z).
    have -> : xev s3 (DVar i) = store_get s3 (keyv i) by [].
    by rewrite (Hfr3 i) // /s''; apply: store_get_set_same.
  have Hacc : (length acc < length l1)%nat /\ (length acc < length l2)%nat.
    by lia.
  set a1 := VArray (map dfst (acc ++ [d]) ++
                    skipn (length (acc ++ [d])) l1)%list.
  set a2 := VArray (map dsnd (acc ++ [d]) ++
                    skipn (length (acc ++ [d])) l2)%list.
  set s4 := store_set s3 (keyv n) a1.
  have Hrun4 : run [DAssign (DAt (DVar n) (DVar i)) vb] s3 = Some s4.
    have G3 : store_get s3 (keyv n) =
              Some (VArray (map dfst acc ++ skipn (length acc) l1)%list).
      by rewrite S3n.
    apply: (run_assign_at _ _ _ _ _ _ _ _ G3 S3i Hvb).
    by rewrite Ez; apply: replace_step; lia.
  (* the tangent written: the tangent of the body, or 0 when it is not varied *)
  have Hav : avoid (keyv n) db.
    move=> x Hx E.
    case: (Hrvd x Hx) => [[p [[Ep | Hp] [Lp [Ex | Ex]]]] | [Hb Hcx]];
      try subst x; try subst p;
      first [ by move: E; rewrite /keyv /n /stored /= => -[]; lia
            | by case: Lp => Lp //; have [_ Hpn] := Hlive_b p Hp Lp;
                 move: E; rewrite /keyv /n /stored /= => -[]
            | by move/keyv_inj: E => /(_ Hcx erefl) E; subst;
                 rewrite /= in Hb; lia ].
  have Hdv : xev s4 (if vr then db else DReal "0") = Some (VReal (dsnd d)).
    case Hvr: (vr); first by rewrite /s4 xev_set_other.
    by rewrite (Hzb Hvr) xev_DReal lit_0.
  have Hrun5 : run [DAssign (DAt (DVar (DotOf n)) (DVar i))
                      (if vr then db else DReal "0")] s4 =
               Some (store_set s4 (keyv (DotOf n)) a2).
    have G4 : store_get s4 (keyv (DotOf n)) =
              Some (VArray (map dsnd acc ++ skipn (length acc) l2)%list).
      rewrite /s4 store_get_set_other; first exact: keyv_dot_neq.
      by rewrite S3d.
    have I4 : xev s4 (DVar i) = Some (VInt z).
      by rewrite /s4 xev_set_other //; move=> x [<- | []]; exact: Kin.
    apply: (run_assign_at _ _ _ _ _ _ _ _ G4 I4 Hdv).
    by rewrite Ez; apply: replace_step; lia.
  exists (store_set s4 (keyv (DotOf n)) a2); split.
    by rewrite /bodyst run_app Hrun3; exact: run_two Hrun4 Hrun5.
  split; first by rewrite length_app /=; lia.
  split.
    apply: frame_set; [| by [] | by right].
    apply: frame_set; [| by [] | by left].
    apply: (frame_chain c (S c) _ s s'' s3 _ Hfr3); last lia.
    by apply: frame_set_fresh => //; rewrite /i /=; lia.
  split.
    rewrite store_get_set_other; first exact: not_eq_sym (keyv_dot_neq n).
    by rewrite /s4 store_get_set_same.
  split; first by rewrite store_get_set_same.
  move=> Hvr; apply/Forall_app; split; first exact: Hzero Hvr.
  by constructor; [exact: Hzb Hvr | constructor].
have [sf [Hex [_ [Hfr [Hn' [Hd' Hzero]]]]]] := Hloop.
rewrite /= in Hn' Hd' Hzero.
have Hlx := eval_map_length _ _ _ _ Hxs.
rewrite Hlx -Hlen1 skipn_all app_nil_r in Hn'.
rewrite Hlx -Hlen2 skipn_all app_nil_r in Hd'.
split; first lia.
split; first by rewrite Hte /= Hlx.
split; first exact: Hzero.
split; first by move=> _; rewrite Hte.
exists sf; split; first by rewrite (run_for _ _ _ _ _ _ 0 h) // Hex.
by split=> // _.
Qed.

(* The body of a fold, opened as the simulation opens it and as well_formed's
   occurs opens it, has the same occurrences. *)
Lemma live_cont2 L k (bP : pv -> pv -> anf pv bare) (bW : vinfo -> vinfo -> anf vinfo bare) x y w1 w2 id :
  (forall i1 i2 s1 s2, anf_eq ((s1, s2) :: (i1, i2) :: gW L) (bP i1 s1) (bW i2 s2)) ->
  Forall (static_ok k) L -> aid (pa x) = k -> aid (pa y) = S k -> vid w1 = k -> vid w2 = S k ->
  occurs_anf id (S (S k)) (bW w1 w2) = occurs_anf id (S (S k)) (bW (anon k) (anon (S k))).
Proof.
move=> HbW HL Hx Hy Hw1 Hw2.
apply: (proj1 occurs_transfer (bP x y) ((y, w2) :: (x, w1) :: gW L)
          ((y, anon (S k)) :: (x, anon k) :: gW L)) => //.
have Ha := aids_below L k HL.
have Hxn : ~ In x L by move=> I; have := Ha _ I; lia.
have Hyn : ~ In y L by move=> I; have := Ha _ I; lia.
have Hxy : x <> y by move=> E; subst; lia.
split.
  by intros p u1 u2 [E1 | [E1 | I1]] [E2 | [E2 | I2]];
    repeat match goal with
    | E : (_, _) = (_, _) |- _ => inversion E; subst; clear E
    | I : In (_, _) (gW L) |- _ => apply in_gW in I; destruct I as [? ?]; subst
    end; rewrite /=; auto; try contradiction; try lia.
by move=> p u [[E | [E | I]] | [E | [E | I]]];
  try (case: E => ? ?; subst; lia); case/in_gW: I => I _; have := Ha _ I; lia.
Qed.

(* A fold: a loop updating the state, a real in a fresh variable, or the
   array updated in place. *)
Lemma sim_fold a (loP hiP initP : atom pv) (bP : pv -> pv -> anf pv bare) :
  (forall x y, sim_body (bP x y)) -> sim_value (AFold a loP hiP initP bP).
Proof.
move=> IHb.
value_intro.
rewrite /= in Htc Hev *.
rename b into bA, b0 into bW, b1 into bT, b2 into bD.
match goal with
  H : forall (i1 : pv) (i2 : avar) (s1 : pv) (s2 : avar), _ |- _ =>
  rename H into HbA end.
match goal with
  H : forall (i1 : pv) (i2 : vinfo) (s1 : pv) (s2 : vinfo), _ |- _ =>
  rename H into HbW end.
match goal with
  H : forall (i1 : pv) (i2 : tvar W) (s1 : pv) (s2 : tvar W), _ |- _ =>
  rename H into HbT end.
match goal with
  H : forall (i1 : pv) (i2 : val (dual R)) (s1 : pv)
             (s2 : val (dual R)), _ |- _ =>
  rename H into HbD end.
have HL := c_static _ _ _ _ _ _ _ _ Hc.
(* the bounds, the initial state *)
move: Htc; case Eb: (ty_eqb (of_atom (amap pw loP)) Integer &&
                     ty_eqb (of_atom (amap pw hiP)) Integer) => // Htc.
have Hlv : forall p, loP = AVar p \/ hiP = AVar p \/ initP = AVar p ->
    In p L /\
    live_value k (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
  by move=> p [E | [E | E]]; subst; split; auto;
    rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
have Hops : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) ->
    forall p, aP = AVar p -> static_ok k p /\ store_ok s p.
  move=> aP HaP p E.
  have HlvP : loP = AVar p \/ hiP = AVar p \/ initP = AVar p.
    by case: HaP => [Ea | [Ea | Ea]]; subst aP; auto.
  have [Hp Lp] := Hlv p HlvP.
  split; first exact: static_in _ _ _ HL Hp.
  exact: c_store _ _ _ _ _ _ _ _ Hc _ Hp Lp.
move: Hev.
case Hlo: (aeval_atom (duals reals) (amap pd loP)) => [[| l | | |] |] //.
case Hhi: (aeval_atom (duals reals) (amap pd hiP)) => [[| h | | |] |] //.
case Hin: (aeval_atom (duals reals) (amap pd initP)) => [s0 |] // Hev.
have Hslo := spell_ok k s loP _ (Hops loP (or_introl erefl)) Hlo.
have Hshi := spell_ok k s hiP _ (Hops hiP (or_intror (or_introl erefl))) Hhi.
have Hsin :=
  spell_ok k s initP _ (Hops initP (or_intror (or_intror erefl))) Hin.
set svr := fold_varied k (amap pa initP) bA in Htc Hev *.
move: Htc; case Er: (ty_eqb (of_atom (amap pw initP)) Real) => Htc.
  (* a real state, at the top *)
  move/ty_eqb_true: Er => Er.
  case: pp Hc Htc => [| | | ix0 sx0] Hc /= Htc //.
  case HtB: (typecheck (option_map (amap pw) wP) ScalarBody (S (S k))
              (bW (VInfo k Integer None) (VInfo (S k) Real None))) Htc
    => [tb [| mm]] Htc; rewrite /= in Htc; try discriminate.
  case Etb: (ty_eqb tb Real) Htc => Htc; rewrite /= in Htc; try discriminate.
  move/ty_eqb_true: Etb => Etb; subst tb; case: Htc => Ete; subst te.
  have Hfresh : forall p, In p L -> pn p <> j.
    move=> p Hp E.
    have Hs : storage wP tail (AFold a loP hiP initP bP) = None.
      by destruct initP as [q | |]; rewrite /= in Er *; rewrite ?Er.
    rewrite Hs in Hst; have [H' _] := Hst p Hp.
    by apply: H'; rewrite /stored E.
  cbn [open_pairs].
  rewrite open_pairs_sbind.
  case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
  have Hc2 : (S c <= c2)%nat.
    by rewrite -[c2]/(snd (sb, (vb, db), c2)) -Hob; exact: open_pairs_mono.
  cbv beta iota.
  set n := DBound (j, j) in Hst Hob *.
  set i := DBound (c, c) in Hob *.
  set bodyst := (sb ++ (if svr then [DAssign (DVar n) vb;
                                      DAssign (DVar (DotOf n)) db]
                        else [DAssign (DVar n) vb]))%list.
  set pre := if svr then [DDefine DMutable n (spell (amap pt initP));
                          DDefine DMutable (DotOf n) (dot (amap pt initP))]
             else [DDefine DMutable n (spell (amap pt initP))].
  cbn [open_pairs].
  change (varied (amap pa initP) ||
          varied_anf (S (S k)) (bA (fresh k) (fresh (S k)))) with svr.
  rewrite (_ : run _ s = run (pre ++ [DFor i (spell (amap pt loP))
                                        (spell (amap pt hiP)) bodyst])%list s).
    by rewrite /tan_fold /pre /bodyst /svr; case: (fold_varied _ _ _).
  (* the initial state *)
  have HopsI := Hops initP (or_intror (or_intror erefl)).
  have Hint : has_type Real s0.
    rewrite -Er.
    exact: (atom_type k initP s0 (fun p E => proj1 (HopsI p E)) Hin).
  destruct s0 as [d0 | | | |]; try contradiction.
  have Hnot : forall aP, (aP = loP \/ aP = hiP \/ aP = initP) ->
      forall p, aP = AVar p -> static_ok k p /\ pn p <> j.
    move=> aP HaP p E; split; first exact: (proj1 (Hops aP HaP p E)).
    have HlvP : loP = AVar p \/ hiP = AVar p \/ initP = AVar p.
      by case: HaP => [Ea | [Ea | Ea]]; subst aP; auto.
    exact: Hfresh (proj1 (Hlv p HlvP)).
  have [L1 [_ [L3 _]]] := avoid_spell k loP j (Hnot loP (or_introl erefl)).
  have [H1' [_ [H3' _]]] :=
    avoid_spell k hiP j (Hnot hiP (or_intror (or_introl erefl))).
  have [I1 [I2 [I3 I4]]] :=
    avoid_spell k initP j (Hnot initP (or_intror (or_intror erefl))).
  have Hdin := dot_ok k s initP _ HopsI Hin.
  set s1 := if svr then store_set (store_set s (keyv n) (VReal (dfst d0)))
                          (keyv (DotOf n)) (VReal (dsnd d0))
            else store_set s (keyv n) (VReal (dfst d0)).
  have Hrun1 : run pre s = Some s1.
    rewrite /pre /s1; case: (svr); last exact: run_define Hsin.
    by apply: run_define2; first exact: Hsin; rewrite xev_set_other.
  have Hlo1 : xev s1 (spell (amap pt loP)) = Some (VInt l).
    by rewrite /s1; case: (svr); rewrite ?xev_set_other.
  have Hhi1 : xev s1 (spell (amap pt hiP)) = Some (VInt h).
    by rewrite /s1; case: (svr); rewrite ?xev_set_other.
  (* the loop *)
  pose Inv := fun (z : Z) (s' : store R) (st : val (dual R)) =>
    frame c (Some n) s s' /\ store_get s' (keyv n) = Some (primal st) /\
    (svr = true -> store_get s' (keyv (DotOf n)) = Some (tangent st)) /\
    has_type Real st /\ (svr = false -> zero st).
  have Hlive_b : forall p, In p L ->
      live_anf (S (S k))
        (bW (VInfo k Integer None) (VInfo (S k) Real None)) p ->
      live_value k
        (AFold Bare (amap pw loP) (amap pw hiP) (amap pw initP) bW) p.
    move=> p Hp Hl; rewrite /live_anf /live_value /= in Hl *.
    by rewrite -(live_cont2 L k bP bW (pfresh k) (pfresh (S k))
                  (VInfo k Integer None) (VInfo (S k) Real None)
                  _ HbW HL erefl erefl erefl erefl) Hl !orb_true_r.
  have Hloop : exists sf,
      exec_up R (run bodyst) (out_dvar nat i) l (count l h) s1 = Some sf /\
      Inv (l + Z.of_nat (count l h))%Z sf ve.
    have Hi1 : Inv l s1 (VReal d0).
      rewrite /Inv /s1; split; last split; last split; last split.
      - case: (svr); last first.
          by apply: frame_set; [exact: frame_refl | by [] | by left].
        apply: frame_set; [| by [] | by right].
        by apply: frame_set; [exact: frame_refl | by [] | by left].
      - case: (svr); last by rewrite store_get_set_same.
        rewrite store_get_set_other; first exact: not_eq_sym (keyv_dot_neq n).
        by rewrite store_get_set_same.
      - by move=> Hs; rewrite Hs store_get_set_same.
      - by [].
      move=> Hs; rewrite /svr /fold_varied in Hs.
      move/orb_false_iff: Hs => [Hs _].
      exact: (atom_zero k initP _ (fun p E => proj1 (HopsI p E)) Hs Hin).
    apply: (fold_loop_sim (fun v w => aeval (duals reals) (bD v w)) (run bodyst)
              (out_dvar nat i) Inv _ _ _ _ _ _ Hi1 Hev).
    move=> z s' st st' [Hfr' [Hn' [Hd' [Hht' Hz']]]] Hbd.
    destruct st as [dst | | | |]; try contradiction.
    set s'' := store_set s' (KVar (out_dvar nat i)) (VInt z).
    set ix := PV (AV k false) (VInfo k Integer None)
                (TVar i Integer None false false false false None) (VInt z) c.
    set sx := PV (AV (S k) svr) (VInfo (S k) Real None)
                (TVar n Real None svr svr svr false None) (VReal dst) j.
    have Kin : keyv i <> keyv n by rewrite /keyv /i /n /= => -[]; lia.
    have Kid : keyv i <> keyv (DotOf n) by rewrite /keyv /i /n.
    have Hctx : ctx_ok (sx :: ix :: L) (S (S k)) (S c) s'' wP PScalar
        (live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) Real None)))
        Real.
      apply: ctx_scalar.
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
        exact: (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
      - move=> p [<- | [<- | Hp]] /=; try lia.
        by move: (c_num _ _ _ _ _ _ _ _ Hc _ Hp) => /=; lia.
      - move=> p [<- | [<- | Hp]] Hl.
        + split; rewrite /s'' /=; first by rewrite store_get_set_other.
          by move=> Hs; rewrite store_get_set_other //; exact: Hd' Hs.
        + by split; first by rewrite /s'' store_get_set_same.
        have Hpn := Hfresh p Hp.
        have Hpc := c_num _ _ _ _ _ _ _ _ Hc _ Hp.
        have [S1 S2] := c_store _ _ _ _ _ _ _ _ Hc _ Hp (Hlive_b p Hp Hl).
        have F1 : store_get s' (keyv (stored p)) =
                  store_get s (keyv (stored p)).
          by apply: Hfr' => //= m [<-]; split; first case.
        have F2 : store_get s' (keyv (DotOf (stored p))) =
                  store_get s (keyv (DotOf (stored p))).
          by apply: Hfr' => //= m [<-]; split; last case.
        rewrite /s''; split.
          rewrite store_get_set_other; last by rewrite F1.
          by rewrite /keyv /stored /= => -[]; lia.
        by move=> Hd; rewrite store_get_set_other // F2; exact: S2.
      move=> a0 E; have [y [-> [Hy Hg]]] := c_written _ _ _ _ _ _ _ _ Hc _ E.
      by exists y; split=> //; split; first by right; right.
    have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) s'' wP PScalar Replay
              (bA (pa ix) (pa sx))
              (bW (VInfo k Integer None) (VInfo (S k) Real None))
              (bT (pt ix) (pt sx)) (bD (VInt z) (VReal dst)) Real st'
              (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _)
              Hctx I HtB Hbd.
    rewrite Hob => -[_ [Hht2 [Hzb [_ [Hrvd [s3 [Hrun3 [Hfr3 [Hvb Hdb]]]]]]]]].
    destruct st' as [dst' | | | |]; try contradiction.
    have S3n : store_get s3 (keyv n) = store_get s' (keyv n).
      rewrite (Hfr3 n) //; first by rewrite /n /=; lia.
      by rewrite /s''; apply: store_get_set_other.
    have Hav : avoid (keyv n) db.
      move=> x Hx E; case: (Hrvd x Hx) => [[p [_ [_ Ex]]] | [Hb Hcx]].
        by subst x; move: E; rewrite /keyv /n.
      by move/keyv_inj: E => /(_ Hcx erefl) E; subst; rewrite /= in Hb; lia.
    set s4 := store_set s3 (keyv n) (VReal (dfst dst')).
    have Hfr4 : frame c (Some n) s s4.
      apply: frame_set; [| by [] | by left].
      apply: (frame_chain c (S c) _ s s'' s3 _ Hfr3); last lia.
      by apply: frame_set_fresh => //; rewrite /i /=; lia.
    have Hzst : svr = false -> zero (VReal dst').
      move=> Hs; apply: Hzb; rewrite /ix /sx /= Hs.
      by move: Hs; rewrite /svr /fold_varied => /orb_false_iff [_ Hs].
    case Hsvr: (svr); last first.
      exists s4; split.
        rewrite /bodyst Hsvr run_app Hrun3.
        by rewrite (run_assign_var _ _ _ (VReal (dfst dst'))).
      split; first exact: Hfr4.
      split; first by rewrite /s4 store_get_set_same.
      by split; first by move=> Hs; rewrite Hs in Hsvr.
    exists (store_set s4 (keyv (DotOf n)) (VReal (dsnd dst'))); split.
      rewrite /bodyst Hsvr run_app Hrun3.
      rewrite (run_assign_var _ _ _ (VReal (dfst dst'))) //.
      rewrite (run_assign_var _ _ _ (VReal (dsnd dst'))) //.
      by rewrite xev_set_other.
    split; first by apply: frame_set; [exact: Hfr4 | by [] | by right].
    split.
      rewrite store_get_set_other; first exact: not_eq_sym (keyv_dot_neq n).
      by rewrite /s4 store_get_set_same.
    split; first by move=> _; rewrite store_get_set_same.
    by split=> // Hs; rewrite Hs in Hsvr.
  have [sf [Hex [Hfrf [Hnf [Hdf [Hhtf Hzf]]]]]] := Hloop.
  split; first lia.
  split; first exact: Hhtf.
  split; first exact: Hzf.
  split; first by move=> _.
  exists sf; split.
    by rewrite run_app Hrun1 (run_for _ _ _ _ _ _ l h Hlo1 Hhi1) Hex.
  split; first exact: Hfrf.
  split; first exact: Hnf.
  case=> Hs; first exact: Hdf Hs.
  exfalso; apply: Hs.
  by destruct initP as [q | |]; rewrite /= in Er *; rewrite ?Er.
(* an array updated in place *)
case Eat: (of_atom (amap pw initP)) Htc => [| | | z] Htc //.
destruct initP as [o | | ]; rewrite /= in Eat Htc; try discriminate.
have Ho : In o L by case: (Hlv o (or_intror (or_intror erefl))).
(* the array is the one the place updates in place *)
have Hown : owner wP pp = Some o /\ tail = true.
  destruct pp as [| | | ix0 sx0]; destruct tail; rewrite /= in Htc;
    try discriminate.
  - destruct wP as [y |] eqn:Ew; rewrite /= in Htc; last discriminate.
    move: Htc; case E: (match amap pw y with
                        | AVar y0 => (vid (pw o) =? vid y0)%nat
                        | _ => false end) => // Htc.
    have [Ey] := unique_written _ _ _ _ _ _ _ _ _ _ Hc Ho erefl E; subst y.
    by rewrite /= Eat.
  move: Htc; case E: (vid (pw o) =? vid (pw sx0))%nat => //= Htc.
  have [_ [Hsx _]] := c_place _ _ _ _ _ _ _ _ Hc.
  by rewrite (same_vid _ _ _ _ _ _ _ _ _ _ Hc Ho Hsx E).
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
(* the array is varied: so is the state *)
have Hlivo : live_value k (AFold Bare (amap pw loP) (amap pw hiP) (AVar (pw o))
                             bW) o.
  by case: (Hlv o (or_intror (or_intror erefl))).
have Hvo : avaried (pa o) = true.
  destruct pp as [| | | ix0 sx0]; rewrite /= in Hown; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate.
    destruct (vty (pw y)); try discriminate.
    case: Hown => Ey; subst y.
    have Hia : is_array (vty (pw o)) by rewrite Eat.
    have [_ [Hv _]] := c_top _ _ _ _ _ _ _ _ Hc o erefl erefl Hia.
    exact: Hv Hlivo.
  case: Hown => Eo; subst sx0.
  by have [_ [_ [_ [_ [Hv _]]]]] := c_place _ _ _ _ _ _ _ _ Hc.
have Hsvr : svr = true by rewrite /svr /fold_varied /= Hvo.
(* the store holds the array and its tangent *)
have [So1 So2] := c_inplace _ _ _ _ _ _ _ _ Hc o o Hown Ho Hlivo erefl.
rewrite /= in Hin; case: Hin => Es0; subst s0.
cbn [open_pairs]; rewrite open_pairs_sbind.
case Hob: (open_pairs _ (S c)) => [[sb [vb db]] c2].
have Hc2 : (S c <= c2)%nat.
  by rewrite -[c2]/(snd (sb, (vb, db), c2)) -Hob; exact: open_pairs_mono.
cbn [open_pairs].
change (varied (amap pa (AVar o)) ||
        varied_anf (S (S k)) (bA (fresh k) (fresh (S k)))) with svr.
set n := DBound (pn o, pn o) in Hob *.
set i := DBound (c, c) in Hob *.
have Hnot : forall aP, (aP = loP \/ aP = hiP) ->
    forall p, aP = AVar p -> static_ok k p /\ pn p <> pn o.
  move=> aP HaP p E.
  have HaP' : aP = loP \/ aP = hiP \/ aP = AVar o by case: HaP; auto.
  split; first exact: (proj1 (Hops aP HaP' p E)).
  move=> Ep.
  have HlvP : loP = AVar p \/ hiP = AVar p \/ AVar o = AVar p.
    by case: HaP => Ea; subst aP; auto.
  have [Hp Lp] := Hlv p HlvP.
  have [Epo | //] := c_owner _ _ _ _ _ _ _ _ Hc o p Hown Hp Ep; subst p.
  have [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]] := static_in _ _ _ HL Ho.
  rewrite Eat in Ht.
  case: HaP => Ea; subst; rewrite /= in Hlo Hhi;
    [case: Hlo => Hlo' | case: Hhi => Hhi']; rewrite ?Hlo' ?Hhi' in Ht;
    exact: Ht.
have Hlive_b : forall p, In p L ->
    live_anf (S (S k)) (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
      p ->
    live_value k (AFold Bare (amap pw loP) (amap pw hiP) (AVar (pw o)) bW) p /\
    pn p <> pn o.
  move=> p Hp Hl.
  have Hcont := live_cont2 L k bP bW (pfresh k) (pfresh (S k))
                  (VInfo k Integer None) (VInfo (S k) (Array z) None)
                  _ HbW HL erefl erefl erefl erefl.
  have Hl' : live_value k (AFold Bare (amap pw loP) (amap pw hiP)
                             (AVar (pw o)) bW) p.
    rewrite /live_anf /live_value /= in Hl *.
    by rewrite -Hcont Hl !orb_true_r.
  split=> // E.
  have [Ep | //] := c_owner _ _ _ _ _ _ _ _ Hc o p Hown Hp E; subst p.
  by rewrite /live_anf Hcont in Hl; congruence.
pose Inv := fun (_ : Z) (s' : store R) (st : val (dual R)) =>
  frame c (Some n) s s' /\ store_get s' (keyv n) = Some (primal st) /\
  store_get s' (keyv (DotOf n)) = Some (tangent st) /\ has_type (Array z) st.
have Hloop : exists sf,
    exec_up R (run sb) (out_dvar nat i) l (count l h) s = Some sf /\
    Inv (l + Z.of_nat (count l h))%Z sf ve.
  have Hi0 : Inv l s (pd o).
    split; first exact: frame_refl.
    split; first exact: So1.
    split; first exact: So2.
    have [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]] := static_in _ _ _ HL Ho.
    by rewrite Eat in Ht.
  apply: (fold_loop_sim (fun v w => aeval (duals reals) (bD v w)) (run sb)
            (out_dvar nat i) Inv _ _ _ _ _ _ Hi0 Hev).
  move=> z0 s' st st' [Hfr' [Hn' [Hd' Hht']]] Hbd.
  set s'' := store_set s' (KVar (out_dvar nat i)) (VInt z0).
  set ix := PV (AV k false) (VInfo k Integer None)
              (TVar i Integer None false false false false None) (VInt z0) c.
  set sx := PV (AV (S k) svr) (VInfo (S k) (Array z) None)
              (TVar n (Array z) None svr svr svr false None) st (pn o).
  have Hpo : (pn o < c)%nat := c_num _ _ _ _ _ _ _ _ Hc _ Ho.
  have Kin : keyv i <> keyv n by rewrite /keyv /i /n /= => -[]; lia.
  have Kid : keyv i <> keyv (DotOf n) by rewrite /keyv /i /n.
  have Hsxs : static_ok (S (S k)) sx.
    repeat split; rewrite /=; auto; try lia; try discriminate;
      try (move=> *; exact I).
    by move=> Hs; change (svr = false) in Hs; congruence.
  have Hixs : static_ok (S (S k)) ix.
    by repeat split; rewrite /=; auto; try lia; discriminate.
  have Hctx : ctx_ok (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx)
      (live_anf (S (S k)) (bW (VInfo k Integer None)
                              (VInfo (S k) (Array z) None)))
      (Array z).
    constructor.
    - constructor=> //; constructor=> //; apply: (Forall_impl _ _ HL) => p Hp.
      by apply: (static_mono k _ p Hp); lia.
    - move=> p q [Ep | [Ep | Hp]] [Eq | [Eq | Hq]] E; try subst p; try subst q;
        rewrite /= in E; try reflexivity; try lia;
        try (have [_ [Hq' _]] := static_in _ _ _ HL Hq; lia);
        try (have [_ [Hp' _]] := static_in _ _ _ HL Hp; lia).
      exact: (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
    - move=> p [<- | [<- | Hp]] /=; try lia.
      by move: (c_num _ _ _ _ _ _ _ _ Hc _ Hp) => /=; lia.
    - move=> p [<- | [<- | Hp]] Hl.
      + by split; rewrite /s'' /= store_get_set_other.
      + by split; first by rewrite /s'' store_get_set_same.
      have [Hl' Hpn] := Hlive_b p Hp Hl.
      have Hpc := c_num _ _ _ _ _ _ _ _ Hc _ Hp.
      have [S1 S2] := c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl'.
      have F1 : store_get s' (keyv (stored p)) = store_get s (keyv (stored p)).
        by apply: Hfr' => //= m [<-]; split; first case.
      have F2 : store_get s' (keyv (DotOf (stored p))) =
                store_get s (keyv (DotOf (stored p))).
        by apply: Hfr' => //= m [<-]; split; last case.
      rewrite /s''; split.
        rewrite store_get_set_other; last by rewrite F1.
        by rewrite /keyv /stored /= => -[]; lia.
      by move=> Hd; rewrite store_get_set_other // F2; exact: S2.
    - move=> a0 E; have [y [-> [Hy Hg]]] := c_written _ _ _ _ _ _ _ _ Hc _ E.
      by exists y; split=> //; split; first by right; right.
    - by rewrite /=; repeat split; auto; change (svr = true); exact: Hsvr.
    - move=> o' p Ho' Hp Ep; rewrite /= in Ho'; case: Ho' => Eo'; subst o'.
      case: Hp => [Ep' | [Ep' | Hp]]; try subst p;
        [by left | by rewrite /= in Ep; lia |].
      by right=> Hl; have [_ Hpn] := Hlive_b p Hp Hl; rewrite /= in Ep.
    - move=> o' p Ho' Hp Lp Ep; rewrite /= in Ho'; case: Ho' => Eo'; subst o'.
      case: Hp => [Ep' | [Ep' | Hp]]; try subst p;
        [| by rewrite /= in Ep; lia |].
        by split; rewrite /s'' /= store_get_set_other.
      by have [_ Hpn] := Hlive_b p Hp Lp; rewrite /= in Ep.
    - move=> p o' Hp Lp Ha Hg Ho'; rewrite /= in Ho'; case: Ho' => Eo'.
      subst o'; case: Hp => [Ep' | [Ep' | Hp]]; try subst p;
        [by [] | by case: Ha |].
      have [Hl' _] := Hlive_b p Hp Lp.
      exact: (c_arrays _ _ _ _ _ _ _ _ Hc p o Hp Hl' Ha Hg Hown).
    - by [].
    by [].
  have := IHb ix sx (sx :: ix :: L) (S (S k)) (S c) s'' wP (PArray ix sx) Replay
            (bA (pa ix) (pa sx))
            (bW (VInfo k Integer None) (VInfo (S k) (Array z) None))
            (bT (pt ix) (pt sx)) (bD (VInt z0) st) (Array z) st'
            (HbA ix _ sx _) (HbW ix _ sx _) (HbT ix _ sx _) (HbD ix _ sx _)
            Hctx I HtB Hbd.
  rewrite Hob => -[_ [Hht2 [_ [_ [_ [s3 [Hrun3 [Hfr3 Hout]]]]]]]].
  have [o' [Eo' [Hn3 Hd3]]] := Hout.
  rewrite /= in Eo'; case: Eo' => Eo'; subst o'.
  exists s3; split; first exact: Hrun3.
  split; last by split; [exact: Hn3 | split; [exact: Hd3 | exact: Hht2]].
  apply: (frame_chain_same c (S c) _ s s'' s3 _ Hfr3); last lia.
  by apply: frame_set_fresh => //; rewrite /i /=; lia.
have [sf [Hex [Hfrf [Hnf [Hdf Hhtf]]]]] := Hloop.
split; first lia.
split; first exact: Hhtf.
split; first by move=> Hs; rewrite Hs in Hsvr.
split; first by move=> _.
exists sf; split; first by rewrite (run_for _ _ _ _ _ _ l h Hslo Hshi) Hex.
by split=> // _.
Qed.

(* ---------------------------------------------------------------------------
   The simulation holds for every body and every value: by induction on the
   pv instance, one case per construct. *)

Theorem simulation :
  (forall bP : anf pv bare, sim_body bP) /\ (forall eP : value pv bare, sim_value eP).
Proof.
apply: anf_value_ind.
- by move=> a e IHe b IHb; case: a => *; apply: sim_let.
- by move=> a; apply: sim_ret.
- by move=> f a; apply: sim_op1.
- by move=> f a b; apply: sim_op2.
- by move=> a i; apply: sim_get.
- by move=> a i v; apply: sim_set.
- by move=> c t IHt e IHe; apply: sim_ite.
- by move=> lo hi b IHb; apply: sim_map.
by move=> a lo hi init b IHb; apply: sim_fold.
Qed.
